/-
**`treiber_aba_tagged.kl`, part 5: thread `1`'s run**
on `EnvGCAdj isa Arch.tso 1 plan0` by `vcgen`.

Thread `1` runs `abaCodeV` (`X64VecTreiberABARun.lean`) from `p1` to `done`;
its fragment `abaCode1` is the code from `p1:` on (`abaCodeV.drop 14`). The
table (`p1Table`): the private stack `Stk` throughout, and

- `A1` at `p1` and `p1pop1` (no write yet),
- `Mid1a` at `p1pop2` (the first pop's record, `r12` its node or `0`),
- `Mid1b` at `p1push` (both pops' records, `r13` the second's node or `0`),
- `Push1` at `p1push1` (`r12 ≠ 0`, the node bounds fixed),
- `Done1` at `done`.

`p1V_envGCAdj`: from `A1` at `p1`, every run that reaches `done` is in
`Done1` (counted, partial).
-/
import Kraken.Promising.SLR.EnvG.X64VecTreiberABARun

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.VecABA

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## Steps of thread `1` -/

theorem Com.node {P : Params} {w : Nat} {S' : BitVec 64 → Prop} {p x : BitVec 64} {σ σ' : EStateX}
    (h : Com P w σ)
    (hn : (S' p ∧ σ' = σ) ∨ ∃ u, (EW w).step (.load .plain false p 8) σ u σ' ∧ x = BitVec.setWidth 64 u) :
    Com P w σ' := by
  rcases hn with ⟨-, rfl⟩ | ⟨u, hs, -⟩
  · exact h
  · exact (ld_step h hs).1

theorem Com.store1 {P : Params} {S' : BitVec 64 → Prop} {p : BitVec 64} {v : Val} {σ σ' : EStateX}
    (h : Com P 1 σ) (hs : (S' p ∧ σ' = σ) ∨ ∃ b, (EW 1).step (.store .plain false p 8 v) σ b σ') :
    Com P 1 σ' := by
  rcases hs with ⟨-, rfl⟩ | ⟨b, hs⟩
  · exact h
  · exact (st_step h hs).1

/-- **The node store** `movq %rax,(%r12)` of a counted run: to the stack
(`p ∈ S`, the environment state unchanged, `dmem` updated within `S`) or a
shared step (`dmem` unchanged). -/
theorem stCase {E : SharedEnv} {S : BitVec 64 → Prop} {d m : Mem 64} {a a' r r' : BitVec 64}
    {g g' : (SharedEnv.counted E).State} (hd : DomIn S d) (ea : a = a') (er : r = r')
    (h : ((Mem.loadInt d a 8).isSome = true ∧ m = Mem.storeInt d a 8 r.toInt ∧ g' = g) ∨
      (Mem.loadInt d a 8 = none ∧ m = d ∧ ∃ ok, E.step (.store .plain false a 8 (r.setWidth 128)) g.1 ok g'.1 ∧
        g'.2 = g.2 + (SharedAccess.store .plain false a 8 (r.setWidth 128)).tick)) :
    ((S a' ∧ g'.1 = g.1) ∨ ∃ b, E.step (.store .plain false a' 8 (r'.setWidth 128)) g.1 b g'.1) ∧ g.2 ≤ g'.2 ∧
      DomIn S m ∧ ∀ b n, (Mem.loadInt d b n).isSome = true → (Mem.loadInt m b n).isSome = true := by
  subst ea er
  rcases h with ⟨hs, rfl, rfl⟩ | ⟨-, rfl, ok, hst, ht⟩
  · exact ⟨.inl ⟨hd.mem_of_loadInt hs (by decide), rfl⟩, Nat.le_refl _, hd.storeInt hs _,
      fun b n hb => Mem.SubDom.loadInt_isSome (Mem.SubDom.storeInt (Mem.SubDom.refl d) a 8 _) hb⟩
  · exact ⟨.inr ⟨ok, hst⟩, by rw [ht]; exact Nat.le_add_right _ _, hd, fun _ _ hb => hb⟩

/-- `Stk` from the domain and the slot. -/
theorem Stk.ofDom {S : BitVec 64 → Prop} {h : BitVec 64} {s s' : MachineData} (hs : Stk S h s)
    (hr : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hD : DomIn S s'.dmem)
    (hsl : (Mem.loadInt s'.dmem (s.regs.get64 .rsp + (-16 : Int64).toBitVec) 16).isSome = true) : Stk S h s' := by
  unfold Stk
  rw [hr]
  exact ⟨hD, hsl, hs.2.2.1, hs.2.2.2⟩

/-! ## The fragment -/

/-- **Thread `1`'s fragment**: the code from `p1:` on. -/
def abaCode1 : Program := abaCodeV.drop 14

theorem abaCode1_eq : abaCode1 = Directive.label "p1" :: abaCode1.tail := by decide
theorem abaCode1_wf : Program.WF abaCode1 := by decide
theorem abaCode1_sub : Program.subBlocksOfE abaCode1 abaImageV = true := by decide

variable [layout : _root_.Layout] [Executable.ValidLayout (layout abaImageV)]

local instance abaImageV.env1 : CodeEnv := ⟨layout abaImageV⟩

theorem abaCode1_placedIn : Program.PlacedIn abaCode1 :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := abaImageV) abaImageV_wf rfl (by decide))
    abaCode1_sub

omit [Executable.ValidLayout (layout abaImageV)] in
theorem abaCode1_last : ∀ l blk, Program.blockAt abaCode1 l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labV "done" :=
  Program.after_last_of (by decide)

/-- Thread `1`'s table. -/
abbrev p1Table (S : BitVec 64 → Prop) :
    Label → MachineData → (SharedEnv.counted (EW 1)).State → Prop :=
  fun lb s σ => Stk S (symV "head") s ∧
    ((lb = "p1" ∧ A1 abaP σ.1) ∨ (lb = "p1pop1" ∧ A1 abaP σ.1) ∨
      (lb = "p1pop2" ∧ Mid1a abaP S σ.1 (s.regs.get64 .r12)) ∨
      (lb = "p1push" ∧ Mid1b abaP S σ.1 (s.regs.get64 .r12) (s.regs.get64 .r13)) ∨
      (lb = "p1push1" ∧ Push1 abaP S σ.1 (s.regs.get64 .r12) (s.regs.get64 .r13)) ∨
      (lb = "done" ∧ Done1 abaP S σ.1 (s.regs.get64 .r12) (s.regs.get64 .r13)))

set_option maxHeartbeats 8000000 in
/-- **Thread `1`'s verbatim run on `EnvGCAdj`** (counted, partial): from
`A1` at `p1`, every run that reaches `done` is in `Done1`. -/
theorem p1V_envGCAdj (S : BitVec 64 → Prop) (hal : isAligned 16 (symV "head") = true) :
    ∀ s g, Stk S (symV "head") s ∧ A1 abaP g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EW 1)))
        (fun x => (x.1.2 = labV "done" ∧ Done1 abaP S x.2.1 (x.1.1.regs.get64 .r12) (x.1.1.regs.get64 .r13)) ∨
          False)
        ((s, labV "p1"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EW 1))
    (Q := fun s σ => Done1 abaP S σ.1 (s.regs.get64 .r12) (s.regs.get64 .r13)) (E := fun _ _ _ => False)
    (p1Table S) ?_ abaCode1_eq abaCode1_wf abaCode1_placedIn abaCode1_last s g
    (by simpa [p1Table] using hsg)
  cfg_cases_env [abaCode1]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hstk, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_envGCAdjX, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  case vc1 => exact ⟨hstk, .inr (.inl ⟨trivial, hT⟩)⟩
  case vc1 => exact hal
  case vc2 => exact hstk.hd_none
  case vc3 => trivial
  case vc4 => exact hstk.2.2.1
  case vc5 => exact hstk.2.1
  case vc6 => trivial
  case vc7 => trivial
  case vc8 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 g4b af g5 hz g6 hld hf1 hm1 hm2 hf0 hf2 hf3 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    simp [CondCode.interp, StatusFlags.from_result] at hz
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨Stk.slot hstk (by simp) rfl, .inr (.inr (.inl ⟨rfl, ?_⟩))⟩, .inl (by decide)⟩
    simp only [Reg64s.get64_set64, ↓reduceIte]
    exact ((((hT.empty hld.1 hz).fence hf1.1).fence hf0.1).fence hf2.1).fence hf3.1
  case vc9 => trivial
  case vc10 => exact hal
  case vc11 => exact (Stk.store hstk.1 hstk.2.1 hstk.2.1).1.loadInt_none hstk.2.2.2 (by decide)
  case vc12 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 g4b af g5 hz g6 u g7 g8 hld hf1 hm1 hm2 hf0 hf2 hf3 hnode hf4 _
    obtain ⟨hn, -⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    exact cas_ok ((((((hd_ld hT.1 hld.1).1.fence hf1.1).fence hf0.1).fence hf2.1).fence hf3.1).node hn |>.fence hf4.1) _
  case vc13 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 g4b af g5 hz g6 u g7 g8 old g9 heq hnz g10 hld hf1 hm1 hm2 hf0 hf2 hf3 hnode hf4 hcas hf5 _
    simp [CondCode.interp] at hnz
  case vc14 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 g4b af g5 hz g6 u g7 g8 old g9 heq hnz g10 g11 hld hf1 hm1 hm2 hf0 hf2 hf3 hnode hf4 hcas hf5 hf6 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    simp [CondCode.interp, StatusFlags.from_result] at hz
    obtain ⟨hn, hcnt⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
    have hn := nodeAddr (p' := lo v) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact BitVec.add_zero _) hn
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at heq
    rw [hi_lo] at heq
    have hc := stepR' hcas.1 rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact op_cas16 v u)
    rcases hT.pop hz hld.1 (((hf1.1.trans hf0.1).trans hf2.1).trans hf3.1) hn hf4.1 hc with ⟨hne, -⟩ | ⟨-, hM⟩
    · exact absurd heq hne
    refine ⟨Stk.slot hstk (by simp) rfl, .inr (.inr (.inl ⟨trivial, ?_⟩))⟩
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    exact (hM.fence hf5.1).fence hf6.1
  case vc15 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 g4b af g5 hz g6 u g7 g8 old g9 heq hnz g10 hld hf1 hm1 hm2 hf0 hf2 hf3 hnode hf4 hcas hf5 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    simp [CondCode.interp, StatusFlags.from_result] at hz
    obtain ⟨hn, hcnt⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
    have hn := nodeAddr (p' := lo v) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact BitVec.add_zero _) hn
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at heq
    rw [hi_lo] at heq
    have hc := stepR' hcas.1 rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact op_cas16 v u)
    rcases hT.pop hz hld.1 (((hf1.1.trans hf0.1).trans hf2.1).trans hf3.1) hn hf4.1 hc with ⟨-, hA⟩ | ⟨heq', -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨Stk.slot hstk (by simp) rfl, .inr (.inl ⟨rfl, ?_⟩)⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      · exact hA.fence hf5.1
      subst hg
      have h1 := hld.2; have h3 := hcas.2
      have := hf1.2; have := hf0.2; have := hf2.2; have := hf3.2; have := hf4.2; have := hf5.2
      simp only [SharedAccess.tick] at h1 h3
      omega
    · exact absurd heq' heq
  case vc16 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 g4b af g5 hz g6 u g7 g8 old g9 heq hnz g10 g11 hld hf1 hm1 hm2 hf0 hf2 hf3 hnode hf4 hcas hf5 hf6 _
    simp [CondCode.interp] at hnz
  case vc1 => exact hal
  case vc2 => exact hstk.hd_none
  case vc3 => trivial
  case vc4 => exact hstk.2.2.1
  case vc5 => exact hstk.2.1
  case vc6 => trivial
  case vc7 => trivial
  case vc8 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 g4b af g5 hz g6 hld hf1 hm1 hm2 hf0 hf2 hf3 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    simp [CondCode.interp, StatusFlags.from_result] at hz
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨Stk.slot hstk (by simp) rfl, .inr (.inr (.inr (.inl ⟨rfl, ?_⟩)))⟩, .inl (by decide)⟩
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    exact ((((hT.empty hld.1).fence hf1.1).fence hf0.1).fence hf2.1).fence hf3.1
  case vc9 => trivial
  case vc10 => exact hal
  case vc11 => exact (Stk.store hstk.1 hstk.2.1 hstk.2.1).1.loadInt_none hstk.2.2.2 (by decide)
  case vc12 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 g4b af g5 hz g6 u g7 g8 hld hf1 hm1 hm2 hf0 hf2 hf3 hnode hf4 _
    obtain ⟨hn, -⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    exact cas_ok ((((((hd_ld hT.1 hld.1).1.fence hf1.1).fence hf0.1).fence hf2.1).fence hf3.1).node hn |>.fence hf4.1) _
  case vc13 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 g4b af g5 hz g6 u g7 g8 old g9 heq hnz g10 hld hf1 hm1 hm2 hf0 hf2 hf3 hnode hf4 hcas hf5 _
    simp [CondCode.interp] at hnz
  case vc14 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 g4b af g5 hz g6 u g7 g8 old g9 heq hnz g10 g11 hld hf1 hm1 hm2 hf0 hf2 hf3 hnode hf4 hcas hf5 hf6 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    simp [CondCode.interp, StatusFlags.from_result] at hz
    obtain ⟨hn, hcnt⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
    have hn := nodeAddr (p' := lo v) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact BitVec.add_zero _) hn
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at heq
    rw [hi_lo] at heq
    have hc := stepR' hcas.1 rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact op_cas16 v u)
    rcases hT.pop hz hld.1 (((hf1.1.trans hf0.1).trans hf2.1).trans hf3.1) hn hf4.1 hc with ⟨hne, -⟩ | ⟨-, hM⟩
    · exact absurd heq hne
    refine ⟨Stk.slot hstk (by simp) rfl, .inr (.inr (.inr (.inl ⟨trivial, ?_⟩)))⟩
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    exact (hM.fence hf5.1).fence hf6.1
  case vc15 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 g4b af g5 hz g6 u g7 g8 old g9 heq hnz g10 hld hf1 hm1 hm2 hf0 hf2 hf3 hnode hf4 hcas hf5 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    simp [CondCode.interp, StatusFlags.from_result] at hz
    obtain ⟨hn, hcnt⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
    have hn := nodeAddr (p' := lo v) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact BitVec.add_zero _) hn
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at heq
    rw [hi_lo] at heq
    have hc := stepR' hcas.1 rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact op_cas16 v u)
    rcases hT.pop hz hld.1 (((hf1.1.trans hf0.1).trans hf2.1).trans hf3.1) hn hf4.1 hc with ⟨-, hA⟩ | ⟨heq', -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨Stk.slot hstk (by simp) rfl, .inr (.inr (.inl ⟨rfl, ?_⟩))⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact hA.fence hf5.1
      subst hg
      have h1 := hld.2; have h3 := hcas.2
      have := hf1.2; have := hf0.2; have := hf2.2; have := hf3.2; have := hf4.2; have := hf5.2
      simp only [SharedAccess.tick] at h1 h3
      omega
    · exact absurd heq' heq
  case vc16 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 g4b af g5 hz g6 u g7 g8 old g9 heq hnz g10 g11 hld hf1 hm1 hm2 hf0 hf2 hf3 hnode hf4 hcas hf5 hf6 _
    simp [CondCode.interp] at hnz
  case vc1 =>
    rename_i s1 g0 af g1 hz g2 hf1 hf2 _
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hstk, .inr (.inr (.inr (.inr (.inr ⟨rfl, ((hT.done hz).fence hf1.1).fence hf2.1⟩))))⟩,
      .inl (by decide)⟩
  case vc2 =>
    rename_i s1 g0 af g1 hz g2 hf1 hf2 _
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact ⟨hstk, .inr (.inr (.inr (.inr (.inl ⟨trivial, ((hT.push hz).fence hf1.1).fence hf2.1⟩))))⟩
  case vc1 => exact hal
  case vc2 => exact hstk.hd_none
  case vc3 => trivial
  case vc4 => exact hstk.2.2.1
  case vc5 => exact hstk.2.1
  case vc6 => trivial
  case vc7 => trivial
  case vc8 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 hnone hld hf1 hm1 hm2 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    exact st_ok ((hd_ld hT.1 hld.1).1.fence hf1.1) _ _
  case vc9 => exact hal
  case vc10 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 dm g5 g6 g7 hld hf1 hm1 hm2 hst hf2 hf3 _
    obtain ⟨-, -, hD, -⟩ := stCase (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 rfl rfl hst
    exact hD.loadInt_none hstk.2.2.2 (by decide)
  case vc11 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 dm g5 g6 g7 hld hf1 hm1 hm2 hst hf2 hf3 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    obtain ⟨hs, -⟩ := stCase (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 rfl rfl hst
    exact cas_ok (((((hd_ld hT.1 hld.1).1.fence hf1.1).store1 hs).fence hf2.1).fence hf3.1) _
  case vc12 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 dm g5 g6 g7 old g8 heq hnz g9 hld hf1 hm1 hm2 hst hf2 hf3 hcas hf4 _
    simp [CondCode.interp] at hnz
  case vc13 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 dm g5 g6 g7 old g8 heq hnz g9 g10 hld hf1 hm1 hm2 hst hf2 hf3 hcas hf4 hf5 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    obtain ⟨hs, hcnt, hD, hmono⟩ := stCase (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 (a' := s1.regs.get64 .r12)
      (r' := lo v) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact BitVec.add_zero _) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) hst
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at heq
    rw [hi_lo] at heq
    have hc := stepR' hcas.1 rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact op_cas16 v (s1.regs.get64 .r12))
    rcases hT.run hld.1 hf1.1 hs (hf2.1.trans hf3.1) hc with ⟨hne, -⟩ | ⟨-, hD1⟩
    · exact absurd heq hne
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨Stk.ofDom hstk (by simp) hD (hmono _ _ (Stk.store hstk.1 hstk.2.1 hstk.2.1).2),
      .inr (.inr (.inr (.inr (.inr ⟨rfl, ?_⟩))))⟩, .inl (by decide)⟩
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    exact (hD1.fence hf4.1).fence hf5.1
  case vc14 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 dm g5 g6 g7 old g8 heq hnz g9 hld hf1 hm1 hm2 hst hf2 hf3 hcas hf4 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    obtain ⟨hs, hcnt, hD, hmono⟩ := stCase (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 (a' := s1.regs.get64 .r12)
      (r' := lo v) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact BitVec.add_zero _) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]) hst
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at heq
    rw [hi_lo] at heq
    have hc := stepR' hcas.1 rfl (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact op_cas16 v (s1.regs.get64 .r12))
    rcases hT.run hld.1 hf1.1 hs (hf2.1.trans hf3.1) hc with ⟨-, hP⟩ | ⟨heq', -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨Stk.ofDom hstk (by simp) hD (hmono _ _ (Stk.store hstk.1 hstk.2.1 hstk.2.1).2),
        .inr (.inr (.inr (.inr (.inl ⟨rfl, ?_⟩))))⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact hP.fence hf4.1
      subst hg
      have h1 := hld.2; have h3 := hcas.2
      have := hf1.2; have := hf2.2; have := hf3.2; have := hf4.2
      simp only [SharedAccess.tick] at h1 h3
      omega
    · exact absurd heq' heq
  case vc15 =>
    rename_i s1 g0 v g1 g2 r1 g3 r2 g4 dm g5 g6 g7 old g8 heq hnz g9 g10 hld hf1 hm1 hm2 hst hf2 hf3 hcas hf4 hf5 _
    simp [CondCode.interp] at hnz
  case vc1 => exact hT

end Kraken.Promising.X64.EnvG.VecABA
