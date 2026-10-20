/-
**Part 4: `main` from the two function
specifications, x64.**

`main` (`Lower/PilotX64Prog.lean`) is a straight line with two `call`s:
`subq $8,%rsp` (the frame: `rsp` 16-byte aligned again at each `call`),
the node from the bump allocator (`rsi := r14`, `r14 += 16`, `ja oom` if past
`r15`), `call push`, `call pop`, the result into `r12`, `addq $8,%rsp`, `ret`.
It is proved by the partial call rule `PartialWpEnv.call`
(`X64/EnvCallsPartial.lean`) at `push_specX` and `pop_specX`
(`Lower/PilotX64Specs.lean`), `vcgen` on the three straight segments, and the
text behind `main` never reached (`main` exits by its `ret`).

The return-address slot of both calls is the 8 bytes at `sp - 16` (`sp` the
entry `rsp`, holding `main`'s own return address); the callee's `Saved`
(`dmem` unchanged) carries the frame across a call, and the two slot stores
lie 16 bytes below `main`'s own return address (`Mem.loadInt_storeInt_of_above`).
`ja oom` is not taken under `r14 + 16 ≤ r15` (`ja_not_taken`).
-/
import Kraken.Promising.Lower.PilotX64Specs

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.DStack

namespace Kraken.Promising.Lower.PilotX

open Kraken.Promising.X64.EnvG.Treiber2X
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The pieces of `main` -/

/-- `main` up to the first `call`. -/
def mainA : Program := parse("
main:
    subq $8, %rsp
    movq %r14, %rsi
    addq $16, %r14
    cmpq %r15, %r14
    ja oom
    movq %rbx, %rdi
")

/-- The first `call`. -/
def callPush : Program := parse("
    call push
")

/-- Between the calls. -/
def mainB : Program := parse("
    movq %rbx, %rdi
")

/-- The second `call`. -/
def callPop : Program := parse("
    call pop
")

/-- `main`'s tail. -/
def mainC : Program := parse("
ret_pop:
    movq %rax, %r12
    addq $8, %rsp
    ret
")

/-- The text behind `main`. -/
def restX : Program := pilotX.drop (mainA ++ callPush ++ mainB ++ callPop ++ mainC).length

theorem pilotX_split : pilotX = (mainA ++ (callPush ++ (mainB ++ (callPop ++ mainC)))) ++ restX := by
  decide

/-! ## Helpers -/

/-- A fragment that never falls through is unaffected by the text behind
it. -/
theorem PartialWpEnv.append_false [CodeEnv] {env : SharedEnv} {q p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {s : MachineData} {g : env.State}
    (h : PartialWpEnv env q (fun _ _ => False) E s g) : PartialWpEnv env (q ++ p) Q E s g := by
  intro pc hpl
  obtain ⟨h1, -, -⟩ := Executable.sits_append cenv q p pc hpl
  exact (h pc h1).mono fun _ hx => hx.elim (fun ⟨_, hf⟩ => hf.elim) .inr

/-- **A straight segment, then the rest**: a `vcgen` triple of the segment
from the exact state `s` (no shared access), its fall-through states `R`
continuing with the rest at every environment state above `g` in the fence
order, its exits `X` exiting with `E` there. -/
theorem PartialWpEnv.seg [CodeEnv] {env : SharedEnv} [env.FenceMonoX] {q p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} {s : MachineData}
    {g : env.State} {R : MachineData → Prop} {X : Int64 → MachineData → Prop}
    (h : ⦃ fun s' => s' = s ⦄ q ⦃ fun _ => R; X ⦄)
    (hk : ∀ s' g', R s' → SharedEnv.FenceMonoX.le g g' → PartialWpEnv env p Q E s' g')
    (hx : ∀ a s' g', X a s' → SharedEnv.FenceMonoX.le g g' → E a s' g') : PartialWpEnv env (q ++ p) Q E s g := by
  refine PartialWpEnv.of_wpEnv fun pc hpl => ?_
  have hI : env.FenceInv (SharedEnv.FenceMonoX.le g) := fun k g' h => SharedEnv.FenceMonoX.fenceInv g k g' h
  exact eventually_weaken _ _ _ _ (fun _ hx' => hx'.imp (fun ⟨ha, hq, hi⟩ => ⟨ha, hk _ _ hq hi⟩)
    (fun ⟨he, hi⟩ => hx _ _ _ he hi))
    (Executable.wpEnv_of_wp hI (h.le_wp s rfl) g (SharedEnv.FenceMonoX.refl g) pc hpl)

/-- **`ja` after `cmp y, x` is not taken when `x ≤ y`.** -/
theorem ja_not_taken {x y : BitVec 64} (h : x ≤ y) (af of : Bool) :
    CondCode.a.interp (StatusFlags.from_result (x - y)
      { cf := (x - y).unsigned != x.unsigned - y.unsigned, af := af, of := of }) = false := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned]
  rcases Nat.lt_or_eq_of_le (BitVec.le_def.mp h) with hlt | heq
  · have := x.isLt
    have := y.isLt
    simp [BitVec.toNat_sub]
    omega
  · obtain rfl := BitVec.eq_of_toNat_eq heq
    simp

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilotX)]

local instance pilotX.env' : CodeEnv := ⟨layout pilotX⟩

/-! ## `main` -/

/-- `main`'s precondition at its entry: `rbx = &top`, `r14` the free node
(with `r14 + 16 ≤ r15`), `main`'s return address `raM` in its slot, the
8 bytes 16 below `rsp` mapped (the callees' return-address slot), the heap off
`dmem`, before the push. -/
def MainPre (P : Params) (w : Nat) (raM : Int64) (s : MachineData) (σ : (SharedEnv.counted (EWV P w)).State) :
    Prop :=
  s.regs.get64 .rbx = P.t ∧ s.regs.get64 .r14 = P.n w ∧ s.regs.get64 .r14 + 16 ≤ s.regs.get64 .r15 ∧
    RetAt s raM ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - 16) 8).isSome = true ∧ HeapOff (HP P) s.dmem ∧
    Pu P w σ.1

/-- `main`'s exit: to `raM`, the popped node in `r12` (`Dn`). -/
def MainE (P : Params) (w : Nat) (raM : Int64) (a : Int64) (s : MachineData)
    (σ : (SharedEnv.counted (EWV P w)).State) : Prop :=
  a = raM ∧ Dn P w (s.regs.get64 .r12) σ.1

theorem main_specX (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (raM : Int64) :
    PartialTripleEnv (SharedEnv.counted (EWV P w)) (MainPre P w raM) pilotX (fun _ _ => False) (MainE P w raM) := by
  rw [pilotX_split]
  refine PartialTripleEnv.of_partialWpEnv fun s g ⟨hbx, h14, h15, ⟨v0, hv0, hra⟩, hsl, hH, hPu⟩ => ?_
  refine PartialWpEnv.append_false ?_
  refine PartialWpEnv.seg (R := fun s₁ => s₁.regs.get64 .rsp = s.regs.get64 .rsp - 8 ∧
      s₁.regs.get64 .rsi = P.n w ∧ s₁.regs.get64 .rdi = P.t ∧ s₁.regs.get64 .rbx = P.t ∧ s₁.dmem = s.dmem)
    (X := fun _ _ => False) ?_ ?_ (fun _ _ _ h _ => h.elim)
  · simp only [mainA]
    vcgen
    case vc1 s' hs hz =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hz
      have e16 : BitVec.setWidth 64 (Int64.toBitVec 16) = 16 := by decide
      rw [e16, BitVec.add_comm, ja_not_taken h15] at hz
      exact Bool.false_ne_true hz
    case vc2 s' hs hz =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hbx, h14, and_true]
      rfl
  rintro s₁ g₁ ⟨h1sp, h1si, h1di, h1bx, h1dm⟩ hle₁
  have e8 : s₁.regs.get64 .rsp - Width.W64.bytesv = s.regs.get64 .rsp - 16 := by
    rw [h1sp, show Width.W64.bytesv = (8 : BitVec 64) from rfl]; bv_omega
  have hsl₁ : (Mem.loadInt s₁.dmem (s₁.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
    rw [e8, h1dm]; exact hsl
  simp only [fenceMonoX_le_counted, fenceMonoX_le_valsEnv] at hle₁
  have h_rt : ∀ (m : DataMem) (a : BitVec 64) (x : Int),
      Mem.loadInt (Mem.storeInt m a 8 x) a 8 = some (Int.ofBytes (Int.toBytes 8 x)) :=
    fun m a x => Mem.loadInt_storeInt m a 8 x (by decide)
  refine PartialWpEnv.call _ _ "push" (push_specX P w hL hw) hsl₁ fun ra => ⟨?_, fun s₂ g₂ hpo => ?_⟩
  · refine ⟨by simpa using h1di, by simpa using h1si, ⟨_, by simpa using h_rt _ _ _, ?_⟩,
      (h1dm ▸ hH : HeapOff (HP P) s₁.dmem).storeInt hsl₁ _, Pu.fence hPu hle₁.1⟩
    simpa using Int64.ofBitVec_ofBytes_toBytes ra
  · obtain ⟨⟨h2bx, -, -, -, -, -, h2dm⟩, h2sp, hPo⟩ := hpo
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at h2bx h2sp h2dm
    show PartialWpEnv _ (mainB ++ (callPop ++ mainC)) _ _ _ _
    refine PartialWpEnv.seg (R := fun s₃ => s₃.regs.get64 .rdi = P.t ∧ s₃.regs.get64 .rsp = s₂.regs.get64 .rsp ∧
        s₃.dmem = s₂.dmem) (X := fun _ _ => False) ?_ ?_ (fun _ _ _ h _ => h.elim)
    · simp only [mainB]
      vcgen
      case vc1 s' hs =>
        subst hs
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h2bx, h1bx, and_true]
    rintro s₃ g₃ ⟨h3di, h3sp, h3dm⟩ hle₃
    simp only [fenceMonoX_le_counted, fenceMonoX_le_valsEnv] at hle₃
    have e3 : s₃.regs.get64 .rsp - Width.W64.bytesv = s₁.regs.get64 .rsp - Width.W64.bytesv := by
      rw [h3sp, h2sp, show Width.W64.bytesv = (8 : BitVec 64) from rfl]; bv_omega
    have hsl₃ : (Mem.loadInt s₃.dmem (s₃.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
      rw [e3, h3dm, h2dm]; exact isSome_loadInt_storeInt hsl₁ _ _ _
    have hH₃ : HeapOff (HP P) s₃.dmem := by
      rw [h3dm, h2dm]; exact (h1dm ▸ hH : HeapOff (HP P) s₁.dmem).storeInt hsl₁ _
    refine PartialWpEnv.call _ _ "pop" (pop_specX P w hL hw) hsl₃ fun ra' => ⟨?_, fun s₄ g₄ hpo' => ?_⟩
    · refine ⟨by simpa using h3di, ⟨_, by simpa using h_rt _ _ _, ?_⟩, hH₃.storeInt hsl₃ _, Po.fence hPo hle₃.1⟩
      simpa using Int64.ofBitVec_ofBytes_toBytes ra'
    obtain ⟨⟨-, -, -, -, -, -, h4dm⟩, h4sp, hDn⟩ := hpo'
    simp only [Reg64s.get64_set64, ↓reduceIte] at h4sp h4dm
    have e4 : 8 + s₄.regs.get64 .rsp = s.regs.get64 .rsp := by
      rw [h4sp, h3sp, h2sp, h1sp]; bv_omega
    have hab : ∀ m (v : Int), Mem.loadInt (Mem.storeInt m (s.regs.get64 .rsp - 16) 8 v) (s.regs.get64 .rsp) 8 =
        Mem.loadInt m (s.regs.get64 .rsp) 8 := fun m v =>
      Mem.loadInt_storeInt_of_above _ _ _ 8 8 _ (by simp; bv_omega) (by simp; bv_omega)
    have hret : Mem.loadInt s₄.dmem (8 + s₄.regs.get64 .rsp) 8 = some v0 := by
      rw [e4, h4dm, h3dm, h2dm, show s₃.regs.get64 .rsp - BitVec.ofNat 64 8 = s.regs.get64 .rsp - 16 from e3.trans e8,
        show s₁.regs.get64 .rsp - Width.W64.bytesv = s.regs.get64 .rsp - 16 from e8, hab, hab, h1dm, hv0]
    show PartialWpEnv _ (mainC ++ []) _ _ _ _
    refine PartialWpEnv.seg (R := fun _ => False)
      (X := fun a s₅ => a = raM ∧ s₅.regs.get64 .r12 = s₄.regs.get64 .rax) ?_ (fun _ _ h _ => h.elim) ?_
    · simp only [mainC]
      vcgen
      case vc1 s' hs =>
        subst hs
        simp only [MachineData.retAddr, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
          show BitVec.setWidth 64 (Int64.toBitVec 8) = 8 from rfl, show Width.W64.bytes = 8 from rfl, hret,
          Option.map_some, Option.isSome_some]
      case vc2 s' hs a ha =>
        subst hs
        simp only [MachineData.retAddr, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
          show BitVec.setWidth 64 (Int64.toBitVec 8) = 8 from rfl, show Width.W64.bytes = 8 from rfl, hret,
          Option.map_some, Option.some.injEq] at ha ⊢
        exact ⟨ha ▸ hra, trivial⟩
    rintro a s₅ g₅ ⟨rfl, h5⟩ hle₅
    simp only [fenceMonoX_le_counted, fenceMonoX_le_valsEnv] at hle₅
    exact ⟨rfl, h5 ▸ (hDn.fence hle₅.1).dn⟩

end Kraken.Promising.Lower.PilotX
