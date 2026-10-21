#!/usr/bin/env python3
"""Enrich source deployments with pinned-compiler, runtime-verified GAS sites.

Usage: python3 tools/enrich_gas_metadata.py --vyper-source vyper-src EXPORT...
EXPORT may be an export JSON file or a directory searched recursively. The
compiler's dependencies must already be installed in the invoking interpreter.
No source bundle, AST, compiler settings, or gas-free export is rewritten.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path, PurePath
import re
import subprocess
import sys


class MetadataError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise MetadataError(message)


def integer(value):
    return type(value) is int


def walk(value, *, source_ast=False):
    if isinstance(value, dict):
        yield value
        for key, child in value.items():
            # ExprNode.to_dict emits folded_value as derived metadata. It can
            # reuse the original node's identity, but is not another source node.
            if not (source_ast and key == "folded_value"):
                yield from walk(child, source_ast=source_ast)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child, source_ast=source_ast)


def is_observation(node):
    value = node.get("value")
    return (
        node.get("ast_type") == "Attribute"
        and node.get("attr") in ("gas", "mana")
        and isinstance(value, dict)
        and value.get("ast_type") == "Name"
        and value.get("id") == "msg"
    )


def ast_evidence(annotated):
    """Index identities in each module, retaining source-independent signatures.

    Standard JSON assigns fresh source IDs (exports often use -1 for the root).
    Only the recompiled identities are used to interpret pc_ast_map. Source
    hashes, node IDs and byte spans tie observations back to the exported AST.
    """
    require(isinstance(annotated, dict), "missing annotated AST")
    imports = annotated.get("imports")
    require(isinstance(imports, list), "missing annotated AST imports")
    modules = [annotated.get("ast"), *imports]
    nodes, observations, signatures = {}, set(), set()
    source_ids = set()
    for module in modules:
        require(isinstance(module, dict) and module.get("ast_type") == "Module",
                "invalid annotated AST module")
        source_id = module.get("source_id")
        digest = module.get("source_sha256sum")
        require(integer(source_id) and source_id not in source_ids,
                "invalid or duplicate AST source ID")
        source_ids.add(source_id)
        require(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest),
                "missing AST source SHA256")
        for node in walk(module, source_ast=True):
            if "ast_type" not in node:
                continue
            node_id = node.get("node_id")
            src = node.get("src")
            require(integer(node_id) and node_id >= 0, "invalid AST node ID")
            require(isinstance(src, str) and re.fullmatch(r"\d+:\d+:-?\d+", src),
                    "invalid AST source span")
            offset, length, node_source_id = map(int, src.split(":"))
            require(node_source_id == source_id, "AST node source ID differs from module")
            identity = (source_id, node_id)
            require(identity not in nodes or nodes[identity] == node,
                    "duplicate AST identity with different nodes")
            nodes[identity] = node
            if is_observation(node):
                observations.add(identity)
                signatures.add((digest, node_id, offset, length, node["attr"]))
    return nodes, observations, signatures


def bytecode(value, label):
    require(isinstance(value, str), f"missing {label}")
    value = value.removeprefix("0x")
    require(len(value) % 2 == 0 and re.fullmatch(r"[0-9a-fA-F]*", value) is not None,
            f"invalid {label}")
    return bytes.fromhex(value)


def gas_sites(source_map, code, nodes, observations):
    require(isinstance(source_map, dict), "missing compiler source map")
    require(source_map.get("pc_ast_map_item_keys") in
            (("source_id", "node_id"), ["source_id", "node_id"]),
            "unsupported pc_ast_map identity schema")
    mapping = source_map.get("pc_ast_map")
    require(isinstance(mapping, dict), "missing pc_ast_map")
    # Decode instruction boundaries so a GAS-valued PUSH immediate is never a site.
    boundaries = set()
    pc = 0
    while pc < len(code):
        boundaries.add(pc)
        opcode = code[pc]
        pc += 1 + (opcode - 0x5f if 0x60 <= opcode <= 0x7f else 0)
    sites = []
    for pc, identity in mapping.items():
        require(integer(pc) and pc >= 0 and pc in boundaries,
                f"source-map PC is not an instruction boundary: {pc!r}")
        require(isinstance(identity, (tuple, list)) and len(identity) == 2
                and all(integer(item) for item in identity),
                f"invalid source-map AST identity at PC {pc}")
        identity = tuple(identity)
        require(identity in nodes, f"unknown source-map AST identity {identity} at PC {pc}")
        if code[pc] == 0x5a and identity in observations:
            sites.append(pc)
    # Unmapped GAS is compiler-generated; mapping to an enclosing node does not
    # make it a source observation. In particular raw_call's default gas is ignored.
    return sorted(sites)


def enrich(trace, compile_bundle):
    annotated = trace.get("annotated_ast")
    require(isinstance(annotated, dict), "source deployment has no annotated AST")
    if not any(is_observation(node) for node in walk(annotated, source_ast=True)):
        for field in ("source_gas_pcs", "source_gas_init_pcs"):
            require(field not in trace or trace[field] == [],
                    f"gas-free source has nonempty {field}")
        return False
    _, _, exported_signatures = ast_evidence(annotated)
    bundle = trace.get("solc_json")
    require(isinstance(bundle, dict), "gas-observing source has no solc_json bundle")
    bundle = copy.deepcopy(bundle)
    sources = bundle.get("sources")
    require(isinstance(sources, dict), "missing solc_json sources")
    source = trace.get("source_code")
    require(isinstance(source, str), "missing deployment source code")
    digest = hashlib.sha256(source.encode()).hexdigest()
    require(annotated["ast"].get("source_sha256sum") == digest,
            "exported AST does not describe deployment source")
    targets = [path for path, item in sources.items()
               if isinstance(item, dict) and item.get("content") == source]
    require(len(targets) == 1, "cannot uniquely identify deployment source in solc_json")
    settings = bundle.get("settings")
    require(isinstance(settings, dict), "missing solc_json settings")
    # Resolved compiler settings retain defaults and custom Venom flags that
    # the standard-JSON settings adapter does not necessarily round-trip.
    resolved = trace.get("compiler_settings")
    require(isinstance(resolved, dict), "missing resolved compiler settings")
    data = compile_bundle(bundle, resolved, targets[0])
    runtime = bytecode(data.get("bytecode_runtime"), "recompiled runtime")
    require(runtime == bytecode(trace.get("runtime_bytecode"), "exported runtime"),
            "pinned compiler runtime differs from export; refusing gas metadata")
    nodes, observations, signatures = ast_evidence(data.get("annotated_ast_dict"))
    require(signatures == exported_signatures,
            "recompiled gas/mana AST observations differ from exported AST")
    sites = gas_sites(data.get("source_map_runtime"), runtime, nodes, observations)
    deployment = bytecode(data.get("bytecode"), "recompiled initcode")
    constructor_sites = gas_sites(data.get("source_map"), deployment, nodes, observations)
    if constructor_sites:
        # Source deployment exports retain constructor calldata both as a
        # separate ABI payload and appended to the transaction initcode.
        # Validate that exact composition; never accept an arbitrary prefix.
        calldata = trace.get("calldata")
        calldata = b"" if calldata is None else bytecode(calldata, "constructor calldata")
        require(deployment + calldata == bytecode(trace.get("initcode"), "exported initcode"),
                "pinned compiler initcode plus constructor calldata differs from export; "
                "refusing constructor gas metadata")
    changed = False
    for field, expected in (("source_gas_pcs", sites),
                            ("source_gas_init_pcs", constructor_sites)):
        if field in trace:
            previous = trace[field]
            require(isinstance(previous, list) and
                    all(integer(pc) and pc >= 0 for pc in previous),
                    f"{field} must be a list of natural PCs")
            require(previous == expected, f"existing {field} differs from pinned compiler evidence")
        else:
            trace[field] = expected
            changed = True
    return changed


def load_compiler(source):
    source = source.resolve(strict=True)
    pin = (Path(__file__).resolve().parents[1] / "VYPER_PIN").read_text().strip()
    require(re.fullmatch(r"[0-9a-f]{40}", pin) is not None, "invalid VYPER_PIN")
    head = subprocess.check_output(
        ["git", "-C", str(source), "rev-parse", "HEAD"], text=True
    ).strip()
    require(head == pin, f"compiler checkout HEAD {head} does not equal VYPER_PIN {pin}")
    # Verify before executing any compiler Python, and never import an ambient
    # installed Vyper in preference to the explicit checkout.
    require((source / "vyper" / "__init__.py").is_file(), "not a Vyper source checkout")
    sys.path.insert(0, str(source))
    from vyper.cli.vyper_json import get_inputs, get_search_paths, get_storage_layout_overrides
    from vyper.compiler.input_bundle import JSONInputBundle
    from vyper.compiler.settings import Settings
    import vyper
    require(Path(vyper.__file__).resolve().is_relative_to(source),
            "imported Vyper is outside the pinned checkout")

    def compile_bundle(bundle, resolved, target):
        require(bundle.get("language") == "Vyper", "solc_json language is not Vyper")
        input_bundle = JSONInputBundle(get_inputs(bundle), search_paths=get_search_paths(bundle))
        target = PurePath(target)
        file_input = input_bundle.load_file(target)
        return vyper.compile_from_file_input(
            file_input,
            input_bundle=input_bundle,
            settings=Settings.from_dict(resolved),
            integrity_sum=bundle.get("integrity"),
            storage_layout_override=get_storage_layout_overrides(bundle).get(target),
            no_bytecode_metadata=not bundle["settings"].get("bytecodeMetadata", True),
            output_formats=["annotated_ast_dict", "bytecode", "bytecode_runtime",
                            "source_map", "source_map_runtime"],
        )

    return compile_bundle


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vyper-source", required=True, type=Path,
                        help="compiler source checkout whose HEAD must equal VYPER_PIN")
    parser.add_argument("exports", nargs="+", type=Path)
    args = parser.parse_args()
    try:
        compile_bundle = load_compiler(args.vyper_source)
        files = set()
        for path in args.exports:
            require(path.exists(), f"export path does not exist: {path}")
            if path.is_dir():
                files.update(path.rglob("*.json"))
            else:
                require(path.is_file() and path.suffix == ".json", f"not an export JSON: {path}")
                files.add(path)
        require(files, "no export JSON files found")
        changed_files, changed_traces = 0, 0
        for path in sorted(files):
            try:
                document = json.loads(path.read_text())
                changes = 0
                for trace in walk(document):
                    if (trace.get("trace_type") == "deployment"
                            and trace.get("deployment_type") == "source"):
                        changes += enrich(trace, compile_bundle)
                if changes:
                    path.write_text(json.dumps(document, indent=2) + "\n")
                    changed_files += 1
                    changed_traces += changes
            except Exception as exc:
                raise MetadataError(f"{path}: {exc}") from exc
        print(f"Enriched {changed_traces} deployment(s) in {changed_files} file(s)")
    except (MetadataError, OSError, subprocess.CalledProcessError, ImportError) as exc:
        parser.exit(1, f"gas metadata enrichment failed: {exc}\n")


if __name__ == "__main__":
    main()
