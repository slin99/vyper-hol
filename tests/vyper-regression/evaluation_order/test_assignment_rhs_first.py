"""Ordinary assignment evaluates the RHS before its target."""

CONTRACT = """
@external
def run() -> uint256[2]:
    indices: DynArray[uint256, 2] = [0, 1]
    result: uint256[2] = [7, 8]
    # RHS pops 1, then target resolution pops 0: result[0] = 1.
    result[indices.pop()] = indices.pop()
    return result
"""


def test_rhs_side_effect_happens_before_target_side_effect(get_contract):
    assert get_contract(CONTRACT).run() == [1, 8]
