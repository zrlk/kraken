/-
`codeAt` on a laid-out executable whose cell list is the code followed by
other cells (the label cells and padding `X64.mkState` places for data
symbols after the code): **an instruction is short of the end of the code**
(`codeAt_ne_prefix_end`), the form of `codeAt_ne_end` for a text that does
not end at the last instruction. The AArch64 twin is
`Kraken/AArch64/WP/CodeAtPrefix.lean`.
-/
import Kraken.CodeAt

namespace Kraken.Executable

private theorem sum_take_succ_le' (l : List (Directive × Nat)) {m : Nat} {c : Directive × Nat}
    (hc : l[m]? = some c) : ((l.take m).map (·.2)).sum + c.2 ≤ (l.map (·.2)).sum := by
  conv => rhs; rw [← List.take_append_drop (m + 1) l]
  rw [List.take_add_one, hc]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]
  omega

/-- **An instruction is short of the end of the code**: in an executable whose
cells are the code `cs` followed by cells `ds` none of which is an
instruction, the address of an instruction `codeAt` finds is not the start
plus the size of `cs`. -/
theorem codeAt_ne_prefix_end (e : Kraken.Executable Directive) [hv : ValidLayout e]
    {cs ds : List (Directive × Nat)} (he : e.2 = cs ++ ds) (hds : ∀ c ∈ ds, ∀ i, c.1 ≠ .instr i)
    {pc : Int64} {i : Instr} {z : Nat} {rest : List (Directive × Nat)}
    (h : e.codeAt pc = (.instr i, z) :: rest) :
    pc ≠ e.1 + .ofNat (cs.map (·.2)).sum := by
  obtain ⟨m, -, rfl, hm, -⟩ := codeAt_pos e h
  have hz : 0 < z := hv.instr_size m _ z hm (fun l => by simp)
  have hmc : m < cs.length := by
    rcases Nat.lt_or_ge m cs.length with hc | hc
    · exact hc
    · rw [he, List.getElem?_append_right hc] at hm
      exact absurd rfl (hds _ (List.mem_of_getElem? hm) i)
  have hcm : cs[m]? = some (.instr i, z) := by rwa [he, List.getElem?_append_left hmc] at hm
  have hle := sum_take_succ_le' cs hcm
  have htot : (cs.map (·.2)).sum ≤ (e.2.map (·.2)).sum := by
    rw [he, List.map_append, List.sum_append]; omega
  have htake : e.2.take m = cs.take m := by rw [he, List.take_append_of_le_length (by omega)]
  have hw := hv.no_wrap
  intro heq
  have h4 := congrArg Int64.toBitVec heq
  simp only [addrOf, sizeBefore, htake, Int64.toBitVec_add, Int64.toBitVec_ofNat'] at h4
  have h5 := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp h4)
  simp only [BitVec.toNat_ofNat] at h5
  simp only at hle
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h5
  omega

end Kraken.Executable
