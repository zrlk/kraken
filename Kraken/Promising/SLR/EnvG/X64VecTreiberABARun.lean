/-
**`treiber_aba_tagged.kl`, part 4: the program, its
image, the private stack slot, and thread `0`'s run** on
`EnvGCAdj isa Arch.tso 0 plan0` by `vcgen`.

The `code` block of `Kraken/Examples/LockFree/X64/treiber_aba_tagged.kl` as
written (`abaCodeV`), run by both threads in its image `abaImageV` (the code,
then the `.kl` runner's data trailer `abaDataV`: `head`, `A`, `B`). Thread `0`
runs from `p0` to `done`; its fragment is the whole code (the block of `p0`
falls through to `p1` in the image's block structure), its table `False` on
thread `1`'s labels (`jmp done` skips them).

- `Stk S h s`: the private stack: `dmem` maps only addresses in `S`, the
  16-byte slot at `-16(%rsp)` is mapped and 16-aligned, `head` is not in
  `S`. `movdqa %xmm0,-16(%rsp)` then `movq -16(%rsp),%rax`,
  `movq -8(%rsp),%rdx` give `rax = lo v`, `rdx = hi v` (`Stk.slot`,
  `rd_lo`, `rd_hi`).
- `p0V_envGCAdj`: from `A0` at `p0`, every run that reaches `done` is in
  `Done0` (counted, partial; `cfgEnv_partial_at`, the absolute 16-byte rules
  of `Kraken/X64VecAbsWP.lean` and the `X64VecTreiberABARec` transitions).
-/
import Kraken.Promising.SLR.EnvG.X64VecTreiberABARec
import Kraken.Promising.SLR.EnvG.X64AdjVCGen
import Kraken.Promising.SLR.EnvG.X64VecPublish
import Kraken.X64VecAbsWP
import Kraken.EnvCfgAbs
import Kraken.SeparationMem
import Kraken.X64.Parser

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.VecABA

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program and its image -/

/-- **The `code` block of `treiber_aba_tagged.kl`, verbatim.** -/
def abaCodeV : Program := parse("
p0:
  movdqa (head),%xmm0
  movdqa %xmm0,-16(%rsp)
  movq -16(%rsp),%rax
  movq -8(%rsp),%rdx
  testq %rax,%rax
  je p0
  movq (%rax),%rbx
  leaq 1(%rdx),%rcx
  lock cmpxchg16b (head)
  jne p0
  movq %rax,%r12
  movq %rbx,%r13
  jmp done
p1:
p1pop1:
  movdqa (head),%xmm0
  movdqa %xmm0,-16(%rsp)
  movq -16(%rsp),%rax
  movq -8(%rsp),%rdx
  movq $0,%r12
  testq %rax,%rax
  je p1pop2
  movq (%rax),%rbx
  leaq 1(%rdx),%rcx
  lock cmpxchg16b (head)
  jne p1pop1
  movq %rax,%r12
p1pop2:
  movdqa (head),%xmm0
  movdqa %xmm0,-16(%rsp)
  movq -16(%rsp),%rax
  movq -8(%rsp),%rdx
  movq $0,%r13
  testq %rax,%rax
  je p1push
  movq (%rax),%rbx
  leaq 1(%rdx),%rcx
  lock cmpxchg16b (head)
  jne p1pop2
  movq %rax,%r13
p1push:
  testq %r12,%r12
  je done
p1push1:
  movdqa (head),%xmm0
  movdqa %xmm0,-16(%rsp)
  movq -16(%rsp),%rax
  movq -8(%rsp),%rdx
  movq %rax,(%r12)
  movq %r12,%rbx
  leaq 1(%rdx),%rcx
  lock cmpxchg16b (head)
  jne p1push1
  jmp done
done:
")

/-- The `.kl` runner's data trailer of `treiber_aba_tagged.kl`: each symbol
a label behind a padding cell, in the order of first mention (`head`, `A`,
`B`). -/
def abaDataV : Program :=
  [.byteArray (.mk #[]), .label "head", .byteArray (.mk #[]), .label "A", .byteArray (.mk #[]), .label "B"]

/-- The image: the code, then the data trailer. -/
def abaImageV : Program := abaCodeV ++ abaDataV

/-- info: 56 -/
#guard_msgs in
#eval abaCodeV.length

theorem abaImageV_wf : Program.WF abaImageV := by decide

theorem abaCodeV_sub : Program.subBlocksOfE abaCodeV abaImageV = true := by decide

/-! ## The private stack slot -/

/-- **The private stack**: `dmem` maps only addresses in `S`; the 16-byte
slot at `-16(%rsp)` is mapped and 16-aligned; `head` is outside `S`. -/
def Stk (S : BitVec 64 → Prop) (h : BitVec 64) (s : MachineData) : Prop :=
  DomIn S s.dmem ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp + (-16 : Int64).toBitVec) 16).isSome = true ∧
    isAligned 16 (s.regs.get64 .rsp + (-16 : Int64).toBitVec) = true ∧ ¬ S h

theorem Stk.hd_none {S : BitVec 64 → Prop} {h : BitVec 64} {s : MachineData} (hs : Stk S h s) :
    Mem.loadInt s.dmem h 16 = none :=
  hs.1.loadInt_none hs.2.2.2 (by decide)

/-- The slot store keeps the stack. -/
theorem Stk.store {S : BitVec 64 → Prop} {a : BitVec 64} {d : Mem 64} {n : Nat} {v : Int}
    (hd : DomIn S d) (hs : (Mem.loadInt d a n).isSome = true) {a' : BitVec 64} {n' : Nat}
    (hs' : (Mem.loadInt d a' n').isSome = true) :
    DomIn S (d.storeInt a n v) ∧ (Mem.loadInt (d.storeInt a n v) a' n').isSome = true :=
  ⟨hd.storeInt hs v, Mem.SubDom.loadInt_isSome (Mem.SubDom.storeInt (Mem.SubDom.refl d) a n v) hs'⟩

theorem neg8_eq : (-8 : Int64).toBitVec = (-16 : Int64).toBitVec + 8 := by decide

/-- **`movq -16(%rsp),%rax` after the slot store** reads the low half. -/
theorem rd_lo {d : Mem 64} {a : BitVec 64} {x : BitVec 128} {r : BitVec 64} {α : Type} {g g' : α} {Q : Prop}
    (h : (∃ w, (d.storeInt a 16 x.toInt).loadInt a 8 = some w ∧ r = BitVec.ofInt 64 w ∧ g' = g) ∨
      ((d.storeInt a 16 x.toInt).loadInt a 8 = none ∧ Q)) : r = lo x ∧ g' = g := by
  rcases h with ⟨w, hw, rfl, rfl⟩ | ⟨hn, -⟩
  · rw [loadInt_store16_lo] at hw
    cases hw
    exact ⟨ofInt_ofBytes8 _, rfl⟩
  · rw [loadInt_store16_lo] at hn; cases hn

/-- **`movq -8(%rsp),%rdx` after the slot store** reads the high half. -/
theorem rd_hi {d : Mem 64} {R : BitVec 64} {x : BitVec 128} {r : BitVec 64} {α : Type} {g g' : α} {Q : Prop}
    (h : (∃ w, (d.storeInt (R + (-16 : Int64).toBitVec) 16 x.toInt).loadInt (R + (-8 : Int64).toBitVec) 8 = some w ∧
        r = BitVec.ofInt 64 w ∧ g' = g) ∨
      ((d.storeInt (R + (-16 : Int64).toBitVec) 16 x.toInt).loadInt (R + (-8 : Int64).toBitVec) 8 = none ∧ Q)) :
    r = hi x ∧ g' = g := by
  rw [neg8_eq, ← BitVec.add_assoc] at h
  rcases h with ⟨w, hw, rfl, rfl⟩ | ⟨hn, -⟩
  · rw [loadInt_store16_hi] at hw
    cases hw
    exact ⟨ofInt_ofBytes8 _, rfl⟩
  · rw [loadInt_store16_hi] at hn; cases hn

/-- **The node load** `movq (%rax),%rbx` of a counted run: from the stack
(`p ∈ S`, the environment state unchanged) or a shared step. -/
theorem nodeLd {E : SharedEnv} {S : BitVec 64 → Prop} {d : Mem 64} {p x : BitVec 64}
    {g g' : (SharedEnv.counted E).State} (hd : DomIn S d)
    (h : (∃ w, Mem.loadInt d p 8 = some w ∧ x = BitVec.ofInt 64 w ∧ g' = g) ∨ (Mem.loadInt d p 8 = none ∧ ∃ u,
      (E.step (.load .plain false p 8) g.1 u g'.1 ∧ g'.2 = g.2 + (SharedAccess.load .plain false p 8).tick) ∧
        x = BitVec.setWidth 64 u)) :
    ((S p ∧ g'.1 = g.1) ∨ ∃ u, E.step (.load .plain false p 8) g.1 u g'.1 ∧ x = BitVec.setWidth 64 u) ∧
      g.2 ≤ g'.2 := by
  rcases h with ⟨w, hw, -, rfl⟩ | ⟨-, u, ⟨hs, ht⟩, rfl⟩
  · exact ⟨.inl ⟨hd.mem_of_loadInt (by rw [hw]; rfl) (by decide), rfl⟩, Nat.le_refl _⟩
  · exact ⟨.inr ⟨u, hs, rfl⟩, by rw [ht]; exact Nat.le_add_right _ _⟩

/-- Transport a node load along an address equation. -/
theorem nodeAddr {E : SharedEnv} {S : BitVec 64 → Prop} {p p' x : BitVec 64} {σ σ' : E.State} (e : p = p')
    (h : (S p ∧ σ' = σ) ∨ ∃ u, E.step (.load .plain false p 8) σ u σ' ∧ x = BitVec.setWidth 64 u) :
    (S p' ∧ σ' = σ) ∨ ∃ u, E.step (.load .plain false p' 8) σ u σ' ∧ x = BitVec.setWidth 64 u := by
  subst e; exact h

/-- Transport an RMW step along address and operation equations. -/
theorem stepR' {E : SharedEnv} {k : RmwKind} {n : Nat} {a a' : BitVec 64} {op op' : Val → Option Val}
    {g g' : E.State} {old : BitVec 128} (h : E.step (.rmw k a n op) g old g') (e : a = a') (e' : op = op') :
    E.step (.rmw k a' n op') g old g' := by
  subst e e'; exact h

/-- `cmpxchg16b`'s operation with `rdx:rax = hi v : lo v` and
`rcx:rbx = (hi v + 1) : x`. -/
theorem op_cas16 (v : Val) (x : BitVec 64) :
    (fun old : BitVec 128 => if (old == hi v ++ lo v) = true then some ((hi v + Int64.toBitVec 1) ++ x) else none) =
      cas16 v ((hi v + 1) ++ x) := by
  funext old
  rw [hi_lo]
  rfl

/-- The slot store keeps `Stk` (`rsp` unchanged). -/
theorem Stk.slot {S : BitVec 64 → Prop} {h : BitVec 64} {s s' : MachineData} {v : Int} (hs : Stk S h s)
    (hr : s'.regs.get64 .rsp = s.regs.get64 .rsp)
    (hd : s'.dmem = s.dmem.storeInt (s.regs.get64 .rsp + (-16 : Int64).toBitVec) 16 v) : Stk S h s' := by
  have h2 := Stk.store hs.1 hs.2.1 hs.2.1 (v := v)
  unfold Stk
  rw [hr, hd]
  exact ⟨h2.1, h2.2, hs.2.2.1, hs.2.2.2⟩

/-- The node load keeps `A0`. -/
theorem A0.node {P : Params} {S' : BitVec 64 → Prop} {p x : BitVec 64} {σ σ' : EStateX} (h : A0 P σ)
    (hn : (S' p ∧ σ' = σ) ∨ ∃ u, (EW 0).step (.load .plain false p 8) σ u σ' ∧ x = BitVec.setWidth 64 u) :
    A0 P σ' := by
  rcases hn with ⟨-, rfl⟩ | ⟨u, hs, -⟩
  · exact h
  · obtain ⟨hc, -, hr, -⟩ := ld_step h.1 hs
    exact ⟨hc, by rw [hr]; exact h.2⟩

/-! ## The symbols -/

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labV (x : Label) : Int64 := (_root_.Executable.labels (layout abaImageV)).label x

/-- A symbol's address in the image. -/
abbrev symV (x : Label) : BitVec 64 := (labV x).toBitVec

/-- The stack's parameters in the image. -/
abbrev abaP : Params := ⟨symV "head", symV "A", symV "B"⟩

variable [Executable.ValidLayout (layout abaImageV)]

local instance abaImageV.env : CodeEnv := ⟨layout abaImageV⟩

theorem abaCodeV_placedIn : Program.PlacedIn abaCodeV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := abaImageV) abaImageV_wf rfl (by decide))
    abaCodeV_sub

omit [Executable.ValidLayout (layout abaImageV)] in
theorem abaCodeV_last : ∀ l blk, Program.blockAt abaCodeV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labV "done" :=
  Program.after_last_of (by decide)

/-! ## Thread `0` -/

/-- Thread `0`'s table: the stack, `A0` at `p0`, `Done0` at `done`. -/
abbrev p0Table (S : BitVec 64 → Prop) :
    Label → MachineData → (SharedEnv.counted (EW 0)).State → Prop :=
  fun lb s σ => Stk S (symV "head") s ∧
    ((lb = "p0" ∧ A0 abaP σ.1) ∨ (lb = "done" ∧ Done0 abaP S σ.1 (s.regs.get64 .r12) (s.regs.get64 .r13)))

set_option maxHeartbeats 4000000 in
/-- **Thread `0`'s verbatim run on `EnvGCAdj`** (counted, partial): from
`A0` at `p0`, every run that reaches `done` is in `Done0`. -/
theorem p0V_envGCAdj (S : BitVec 64 → Prop) (hal : isAligned 16 (symV "head") = true) :
    ∀ s g, Stk S (symV "head") s ∧ A0 abaP g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EW 0)))
        (fun x => (x.1.2 = labV "done" ∧ Done0 abaP S x.2.1 (x.1.1.regs.get64 .r12) (x.1.1.regs.get64 .r13)) ∨ False)
        ((s, labV "p0"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EW 0))
    (Q := fun s σ => Done0 abaP S σ.1 (s.regs.get64 .r12) (s.regs.get64 .r13)) (E := fun _ _ _ => False)
    (p0Table S) ?_ rfl (by decide) abaCodeV_placedIn abaCodeV_last s g (by simpa [p0Table] using hsg)
  cfg_cases_env [abaCodeV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hstk, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_envGCAdjX, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  case vc1 => exact hal
  case vc2 => exact hstk.hd_none
  case vc3 => trivial
  case vc4 => exact hstk.2.2.1
  case vc5 => exact hstk.2.1
  case vc6 => trivial
  case vc7 => trivial
  case vc8 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 af g5 hz g6 hld hf1 hm1 hm2 hf2 hf3 _
    obtain ⟨-, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨-, rfl⟩ := rd_hi hm2
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨Stk.slot hstk (by simp) rfl,
      .inl ⟨rfl, (((hT.ld hld.1).fence hf1.1).fence hf2.1).fence hf3.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have := hf1.2; have := hf2.2; have := hf3.2
    simp only [SharedAccess.tick] at h1
    omega
  case vc9 => trivial
  case vc10 => exact hal
  case vc11 => exact (Stk.store hstk.1 hstk.2.1 hstk.2.1).1.loadInt_none hstk.2.2.2 (by decide)
  case vc12 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 af g5 hz g6 u g7 g8 hld hf1 hm1 hm2 hf2 hf3 hnode hf4 _
    obtain ⟨hn, -⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
    obtain ⟨-, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨-, rfl⟩ := rd_hi hm2
    exact cas_ok ((((((hT.ld hld.1).fence hf1.1).fence hf2.1).fence hf3.1).node hn).fence hf4.1).1 _
  case vc13 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 af g5 hz g6 u g7 g8 old g9 heq hnz g10 hld hf1 hm1 hm2 hf2 hf3 hnode hf4 hcas hf5 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at heq hcas
    simp [CondCode.interp] at hnz
  case vc14 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 af g5 hz g6 u g7 g8 old g9 heq hnz g10 g11 g12 g13 hld hf1 hm1 hm2 hf2 hf3 hnode hf4 hcas hf5 hf6 hf7 hf8 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at heq hcas
    simp [CondCode.interp] at hnz
    obtain ⟨hn, hcnt⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
    have hn := nodeAddr (p' := lo v) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact BitVec.add_zero _) hn
    rw [hi_lo] at heq
    have hc := stepR' hcas.1 rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact op_cas16 v u)
    rcases hT.pop hld.1 ((hf1.1.trans hf2.1).trans hf3.1) hn hf4.1 hc with ⟨hne, -⟩ | ⟨-, hD⟩
    · exact absurd heq hne
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨Stk.slot hstk (by simp) rfl, .inr ⟨rfl, ?_⟩⟩, .inl (by decide)⟩
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    exact (((hD.fence hf5.1).fence hf6.1).fence hf7.1).fence hf8.1
  case vc15 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 af g5 hz g6 u g7 g8 old g9 heq hnz g10 hld hf1 hm1 hm2 hf2 hf3 hnode hf4 hcas hf5 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at heq hcas
    simp [CondCode.interp] at hnz
    obtain ⟨hn, hcnt⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
    have hn := nodeAddr (p' := lo v) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact BitVec.add_zero _) hn
    rw [hi_lo] at heq
    have hc := stepR' hcas.1 rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact op_cas16 v u)
    rcases hT.pop hld.1 ((hf1.1.trans hf2.1).trans hf3.1) hn hf4.1 hc with ⟨-, hA⟩ | ⟨heq', -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨Stk.slot hstk (by simp) rfl, .inl ⟨rfl, hA.fence hf5.1⟩⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have h1 := hld.2; have h3 := hcas.2
      have := hf1.2; have := hf2.2; have := hf3.2; have := hf4.2; have := hf5.2
      simp only [SharedAccess.tick] at h1 h3
      omega
    · exact absurd heq' heq
  case vc16 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 af g5 hz g6 u g7 g8 old g9 heq hnz g10 g11 g12 g13 hld hf1 hm1 hm2 hf2 hf3 hnode hf4 hcas hf5 hf6 hf7 hf8 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at heq hcas
    simp [CondCode.interp] at hnz
  case vc1 => exact hT
  all_goals done

end Kraken.Promising.X64.EnvG.VecABA
