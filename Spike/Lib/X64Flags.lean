/-
**x64 instructions with undefined flags, as nodes of a function**: the
`Out.choice` row on the block machinery of `Spike/Lib/X64Block.lean`.

`and`/`or`/`xor`/`test`/`imul`/shifts leave some status flags undefined;
Kraken's tree at such a cell is a finite choice of `.done` leaves
(`SilentTree`, `Kraken/Promising/Lower/Silent.lean`), so the block lemma's
deterministic abstract run does not cover them. Here each is one
instruction of its own (`FI`): the leaves differ only in the flags, so the
abstract state after it is the destination written (`FI.regs`) and the
flags any `fl`, and a function's node at such an instruction lands at the
next node for every `fl` (`flag_nd`, the `seg_nd` of `Spike/Lib/X64Cfg.lean`
for one instruction). The compiled code reads no flag an `FI` leaves (scc
compares again before every conditional), so the next node's invariant does
not mention them.

Kraken's rows are `Kraken/Promising/Lower/EventsX64Flags.lean` and
`EventsX64Sys.lean` (`exec_and_rr`, `exec_or_rr`, `exec_xor_rr`,
`exec_test_rr`, `silent_imul_rr`, `silent_shl_cl`/`silent_shr_cl` and the
count-0 rows `exec_shl_cl_zero`/`exec_shr_cl_zero`, `exec_xor_rr32_self`);
`exec_fi` puts them in one form. Covered: the register forms scc emits
(`andq`/`orq`/`xorq`/`testq` `%r, %r'`, `imulq %r, %r'`, `shlq`/`shrq %cl,
%r`, and the zeroing `xorl %r32, %r32`).
-/
import Spike.Lib.X64Cfg
import Kraken.Promising.Lower.EventsX64Sys
import Kraken.X64.Parser

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64

/-! ## The instructions -/

/-- **An instruction with an undefined flag** (64-bit register operands). -/
inductive FI where
  /-- `and %s, %d`. -/
  | and_rr (d s : Reg64)
  /-- `or %s, %d`. -/
  | or_rr (d s : Reg64)
  /-- `xor %s, %d`. -/
  | xor_rr (d s : Reg64)
  /-- `test %b, %a`. -/
  | test_rr (a b : Reg64)
  /-- `imul %s, %d`. -/
  | imul_rr (d s : Reg64)
  /-- `shl %cl, %d`. -/
  | shl_cl (d : Reg64)
  /-- `shr %cl, %d`. -/
  | shr_cl (d : Reg64)
  /-- `xor %d32, %d32`: zeroes `d` (the 32-bit write clears the upper half). -/
  | xor_rr32_self (d : Reg64)

/-- The directive. -/
def FI.toDir : FI → Directive
  | .and_rr d s => op64 (.and (.reg (.low d .W64)) (.reg (.low s .W64)))
  | .or_rr d s => op64 (.or (.reg (.low d .W64)) (.reg (.low s .W64)))
  | .xor_rr d s => op64 (.xor (.reg (.low d .W64)) (.reg (.low s .W64)))
  | .test_rr a b => op64 (.test (.reg (.low a .W64)) (.reg (.low b .W64)))
  | .imul_rr d s => op64 (.imul none (.reg (.low d .W64)) (.reg (.low s .W64)))
  | .shl_cl d => op64 (.shl (.reg (.low d .W64)) .cl)
  | .shr_cl d => op64 (.shr (.reg (.low d .W64)) .cl)
  | .xor_rr32_self d => op32 (.xor (.reg (.low d .W32)) (.reg (.low d .W32)))

/-- The count of a shift by `%cl`: the low 8 bits of `%rcx`, masked to 6. -/
abbrev clOf (r : Reg64s) : Nat := ((r.get64 .rcx).take 8).toNat &&& 63

/-- **The registers after it** (the flags aside). -/
def FI.regs : FI → Reg64s → Reg64s
  | .and_rr d s, r => r.set64 d (r.get64 d &&& r.get64 s)
  | .or_rr d s, r => r.set64 d (r.get64 d ||| r.get64 s)
  | .xor_rr d s, r => r.set64 d (r.get64 d ^^^ r.get64 s)
  | .test_rr .., r => r
  | .imul_rr d s, r => r.set64 d (r.get64 d * r.get64 s)
  | .shl_cl d, r => r.set64 d (r.get64 d <<< clOf r)
  | .shr_cl d, r => r.set64 d ((r.get64 d).ushiftRight (clOf r))
  | .xor_rr32_self d, r => r.set64 d 0

/-- The register it writes. -/
def FI.dst : FI → Option Reg64
  | .and_rr d _ | .or_rr d _ | .xor_rr d _ | .imul_rr d _ | .shl_cl d | .shr_cl d | .xor_rr32_self d => some d
  | .test_rr .. => none

/-- The side condition: it does not write `%rsp`. -/
def FI.ok (fi : FI) : Bool := fi.dst != some .rsp

/-- The static offsets after it: the destination forgotten. -/
def FI.so (fi : FI) (o : SO) : SO :=
  match fi.dst with
  | some d => o.kill d
  | none => o

theorem FI.regs_get64 (fi : FI) (r : Reg64s) {x : Reg64} (hx : fi.dst ≠ some x) :
    (fi.regs r).get64 x = r.get64 x := by
  cases fi <;> simp only [FI.dst, ne_eq, Option.some.injEq] at hx <;>
    first | rfl | exact Reg64s.get64_set64_ne _ (Ne.symm hx) _

theorem Reg64s.set64_get64 (s : Reg64s) (r : Reg64) : s.set64 r (s.get64 r) = s := by
  cases r <;> simp [Reg64s.set64, Reg64s.get64]

/-! ## Kraken's step -/

section Exec

variable {st : State}

/-- The machine data after it: registers `FI.regs`, flags `fl`. -/
abbrev FI.post (fi : FI) (m : MachineData) (fl : StatusFlags) : MachineData :=
  { m with regs := fi.regs m.regs, status := fl }

/-- **Kraken's step at an `FI`**: a silent tree whose every leaf is the
registers `FI.regs` and some flags. -/
theorem exec_fi {fi : FI} {z : Nat} (hc : CellAt st fi.toDir z) :
    ∃ t, isa.exec st = some t ∧ SilentTree (fun s' => ∃ fl, s' = after st z (fi.post st.st.1 fl)) t := by
  cases fi with
  | and_rr d s =>
    exact ⟨_, exec_and_rr hc, (silentTree_choose2 _).mono fun _ ⟨_, h⟩ => ⟨_, by
      rw [h]; simp only [logicPost, Reg64s.get_low64]; rfl⟩⟩
  | or_rr d s =>
    exact ⟨_, exec_or_rr hc, (silentTree_choose2 _).mono fun _ ⟨_, h⟩ => ⟨_, by
      rw [h]; simp only [logicPost, Reg64s.get_low64]; rfl⟩⟩
  | xor_rr d s =>
    exact ⟨_, exec_xor_rr hc, (silentTree_choose2 _).mono fun _ ⟨_, h⟩ => ⟨_, by
      rw [h]; simp only [logicPost, Reg64s.get_low64]; rfl⟩⟩
  | test_rr a b =>
    exact ⟨_, exec_test_rr hc, (silentTree_choose2 _).mono fun _ ⟨_, h⟩ => ⟨_, by
      rw [h]; rfl⟩⟩
  | imul_rr d s =>
    obtain ⟨t, hex, hs⟩ := silent_imul_rr hc
    exact ⟨t, hex, hs.mono fun _ ⟨fl, _, _, h⟩ => ⟨fl, by rw [h]; simp only [Reg64s.get_low64]; rfl⟩⟩
  | shl_cl d =>
    by_cases hk : clCount st = 0
    · refine ⟨_, exec_shl_cl_zero hc hk, (silentTree_done _).mono fun _ h => ⟨st.st.1.status, ?_⟩⟩
      have hk' : clOf st.st.1.regs = 0 := hk
      rw [h]; simp only [FI.post, FI.regs, hk', BitVec.shiftLeft_zero, Reg64s.set64_get64]
    · obtain ⟨t, hex, hs⟩ := silent_shl_cl hc hk
      exact ⟨t, hex, hs.mono fun _ ⟨fl, h⟩ => ⟨fl, by rw [h]; simp only [Reg64s.get_low64]; rfl⟩⟩
  | shr_cl d =>
    by_cases hk : clCount st = 0
    · refine ⟨_, exec_shr_cl_zero hc hk, (silentTree_done _).mono fun _ h => ⟨st.st.1.status, ?_⟩⟩
      have hk' : clOf st.st.1.regs = 0 := hk
      have h0 : (st.st.1.regs.get64 d).ushiftRight 0 = st.st.1.regs.get64 d :=
        BitVec.eq_of_toNat_eq (by simp)
      rw [h]; simp only [FI.post, FI.regs, hk', h0, Reg64s.set64_get64]
    · obtain ⟨t, hex, hs⟩ := silent_shr_cl hc hk
      exact ⟨t, hex, hs.mono fun _ ⟨fl, h⟩ => ⟨fl, by rw [h]; simp only [Reg64s.get_low64]; rfl⟩⟩
  | xor_rr32_self d =>
    exact ⟨_, exec_xor_rr32_self hc, (silentTree_choose2 _).mono fun _ ⟨_, h⟩ => ⟨_, by
      rw [h]; simp only [FI.post, FI.regs, Reg64s.set]; rfl⟩⟩

end Exec

/-! ## The abstract state -/

/-- **The abstract state after it**: registers `FI.regs`, flags `fl`. -/
def FI.step (fi : FI) (σ : AS) (fl : StatusFlags) : AS := { σ with regs := fi.regs σ.regs, status := fl }

theorem FI.abs {fi : FI} (hok : fi.ok = true) {R : Region} {o : SO} {m : MachineData} {σ : AS} (hA : Abs R o m σ)
    (fl : StatusFlags) : Abs R (fi.so o) (fi.post m fl) (fi.step σ fl) := by
  refine ⟨by simp only [FI.step, hA.regs], hA.zmms, rfl, ?_, hA.slot⟩
  simp only [FI.so, FI.step]
  split
  · rename_i d hd
    have hdr : d ≠ .rsp := by
      intro h; subst h; rw [FI.ok, hd] at hok; exact absurd hok (by decide)
    refine SORel.write (o := o) (d := d) (by simp [SO.write, hdr]) hA.so fun r hr => fi.regs_get64 _ ?_
    rw [hd]; simpa using Ne.symm hr
  · rename_i hd
    intro r k h
    rw [fi.regs_get64 _ (by rw [hd]; simp)]
    exact hA.so r k h

/-! ## A node at it -/

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at an instruction with an undefined flag**: from every state
of the invariant, for every value of the flags, the state after it lands at
a node, after a local run of the source. Its states lie in `W`, and no
outside move `K` moves them (`hW`). -/
theorem flag_ndW {W : Frag isa} {K : State → State → Prop} {n : ND} {fi : FI} {z : Nat} (hok : fi.ok = true)
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(fi.toDir, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ σ c, n.J σ c → ∀ fl,
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, fi.so n.o, fi.step σ fl⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s fi.toDir z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨t, hex, hs⟩ := exec_fi hc
  refine .choice _ t hex hs fun s' ⟨fl, hs'⟩ => ?_
  obtain ⟨c', hr, hL⟩ := hedge σ c hJ fl
  have hA' := FI.abs hok hA fl
  have hD' : F (fi.post s.st.1 fl) := hF _ _ hD fun _ _ _ => rfl
  refine ⟨c', hr, ?_⟩
  subst hs'
  have hs1 : after s z (fi.post s.st.1 fl) = { s with st := (fi.post s.st.1 fl, n.pc + Int64.ofNat z) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨x, hx⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨x, hx.at he hn hdc hA' hD'⟩

/-- **A node at an instruction with an undefined flag**: from every state
of the invariant, for every value of the flags, the state after it lands at
a node, after a local run of the source. -/
theorem flag_nd {n : ND} {fi : FI} {z : Nat} (hok : fi.ok = true) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(fi.toDir, z)])
    (hedge : ∀ σ c, n.J σ c → ∀ fl,
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, fi.so n.o, fi.step σ fl⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (flag_ndW (W := fun _ _ => True) (K := fun _ _ => False) hok hF hcode NodeW.triv hedge).toSeg

end Fn

/-! ## The parser's forms -/

section Parse

open Kraken.X64.Parser

/-- `FI.toDir` is what Kraken's parser makes of scc's text. -/
example : parse("andq %rcx, %rax
orq %rcx, %rax
xorq %rcx, %rax
testq %rax, %rax
imulq %rcx, %rax
shlq %cl, %rax
shrq %cl, %rax
xorl %ebp, %ebp") = [FI.toDir (.and_rr .rax .rcx), FI.toDir (.or_rr .rax .rcx), FI.toDir (.xor_rr .rax .rcx),
    FI.toDir (.test_rr .rax .rax), FI.toDir (.imul_rr .rax .rcx), FI.toDir (.shl_cl .rax),
    FI.toDir (.shr_cl .rax), FI.toDir (.xor_rr32_self .rbp)] := by
  decide

end Parse

end Spike.Lib.X64
