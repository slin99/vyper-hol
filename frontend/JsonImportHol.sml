(* JsonImportHol.sml - HOL construction backend for the shared JSON decoders. *)
structure JsonImportHol : jsonImportTerm
  where type term = Term.term
  where type hol_type = Type.hol_type = struct

open HolKernel
(* Load the constructor and record metadata used by the shared decoders. *)
open jsonASTTheory

type term = Term.term
type hol_type = Type.hol_type

val constant = prim_mk_const
fun named_type {Thy, Tyop} = mk_thy_type {Thy = Thy, Tyop = Tyop, Args = []}
val bool_ty = Type.bool
val string_ty = stringSyntax.string_ty
val int_ty = intSyntax.int_ty
val num_ty = numSyntax.num
val mk_type = Type.mk_type
val mk_prod = pairSyntax.mk_prod
val mk_option = optionSyntax.mk_option
val word_ty = wordsSyntax.mk_int_word_type
fun word_literal (width, value) =
  wordsSyntax.mk_wordi (Arbnum.fromLargeInt (IntInf.toLarge value), width)
val address_from_hex = vfmTypesSyntax.address_from_hex
val bytes32_from_hex = vfmTypesSyntax.bytes32_from_hex
val bytes_from_hex = byteStringCacheLib.cached_bytes_from_hex
val mk_comb = Term.mk_comb
val list_mk_comb = Term.list_mk_comb
val mk_pair = pairSyntax.mk_pair
val dest_pair = pairSyntax.dest_pair
val mk_list = listSyntax.mk_list
val mk_some = optionSyntax.mk_some
val mk_none = optionSyntax.mk_none
val is_some = optionSyntax.is_some
val dest_some = optionSyntax.dest_some
val mk_bool = boolSyntax.mk_bool
val fromMLstring = stringSyntax.fromMLstring
fun natural value = numSyntax.mk_numeral (Arbnum.fromLargeInt (IntInf.toLarge value))
fun integer value = intSyntax.term_of_int (Arbint.fromLargeInt (IntInf.toLarge value))
val strip_comb = HolKernel.strip_comb
val aconv = Term.aconv
val dest_list = listSyntax.dest_list
(* Match the original validator's string/natural type guard exactly. *)
fun is_atomic tm =
  type_of tm = string_ty orelse
  type_of tm = type_of (numSyntax.term_of_int 0)
val mk_record = TypeBase.mk_record

end
