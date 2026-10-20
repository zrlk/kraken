/-
**Part 2: `enq` and `deq` as x64 fragment
specifications under the register-link convention.**
-/
import Kraken.Promising.Lower.MsqXRProg
import Kraken.Promising.Lower.PilotXRSpecs
import Kraken.Promising.Lower.FragSpecX64

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.MsqXR

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64 sAll mem_sAll8)
open Kraken.Promising.X64.EnvG.Treiber2X (stepL stepR okR)
open Kraken.Promising.Lower.PilotX (Saved Saved.refl)
open Kraken.Promising.Lower.PilotXR (D8 ofBitVec_reg)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## `enq` -/

/-- `enq`'s precondition: link `ra`, `rdi = &tail`, `rsi = n`, `E0` of `n`. -/
def EnqPre (P : Params) (n : BitVec 64) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (EEX P)).State) :
    Prop :=
  t.regs.get64 .r11 = ra.toBitVec ∧ t.regs.get64 .rdi = P.t ∧ t.regs.get64 .rsi = n ∧ D8 t.dmem ∧ E0 P n σ.1

/-- `enq`'s postcondition: the frame kept, `n` linked (`Linked`). -/
def EnqPost (P : Params) (n : BitVec 64) (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (EEX P)).State)
    (s : MachineData) (σ : (SharedEnv.counted (EEX P)).State) : Prop :=
  Saved t s ∧ ∃ y3, Linked P n y3 σ.1

/-- `enq`'s loop table. -/
abbrev enqTable (P : Params) (n : BitVec 64) (ra : Int64) (t : MachineData) (_ : (SharedEnv.counted (EEX P)).State) :
    Label → MachineData → (SharedEnv.counted (EEX P)).State → Prop :=
  fun lb s σ => s.regs.get64 .r11 = ra.toBitVec ∧ s.regs.get64 .rdi = P.t ∧ s.regs.get64 .rsi = n ∧
    Saved t s ∧ D8 s.dmem ∧
    ((lb = "enq" ∧ E0 P n σ.1) ∨
      (lb = "enq_swing" ∧ ∃ y3 y4, s.regs.get64 .rdx = BitVec.setWidth 64 y3 ∧
        s.regs.get64 .rcx = BitVec.setWidth 64 y4 ∧ BitVec.setWidth 64 y4 ≠ 0 ∧ E2 P n y3 y4 σ.1))

open Lean Elab Tactic in
/-- The counts of the run's fences and RMWs (for a back edge's `omega`). -/
local elab "fen_all" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let e ← Term.exprToSyntax d.toExpr
    let isFen : Bool := match ty.getAppFn.constName? with
      | some (.str n "le") => (n.toString.splitOn "FenceMono").length > 1 | _ => false
    if isFen then evalTactic (← `(tactic| have := (fenC $e).2))
    else if ty.isAppOf ``SharedEnv.step then
      try evalTactic (← `(tactic| have := by with_reducible exact (rmwC $e).2)) catch _ => pure ()

set_option hygiene false in
/-- The registers of the table, the frame `Saved`, after a block (only
caller-saved registers written). -/
local macro "regs_kept" : tactic => `(tactic| (
  all_goals first
    | (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; first | assumption | exact ofBitVec_reg h11)
    | skip))

set_option hygiene false in
/-- `enq`'s three reads: `h3 : E2` after them. -/
local macro "e_reads" : tactic => `(tactic| (
  obtain ⟨w3, hs1, c1, e3⟩ := ldC hd8 ld1
  have h1 := vc_e_load_tail _ hT w3 g1.1 (stepL hs1 (by simp [hdi', Params.tail]))
  obtain ⟨w4, hs2, c2, e4⟩ := ldC hd8 ld2
  have h2 := vc_e_load_link _ h1 w4 g2.1 (stepL hs2 (by simp [e3]))
  obtain ⟨w5, hs3, c3, e5⟩ := ldC hd8 ld3
  have h3 := vc_e_load2 _ h2 w5 g3.1 hs3))

set_option hygiene false in
/-- Land at `enq` with `E0` `t` (a back edge: the count went up). -/
local macro "to_enq" t:term : tactic => `(tactic| (
  dsimp only
  refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8,
    .inl ⟨rfl, $t⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
  regs_kept))

set_option hygiene false in
/-- A path through a `lock cmpxchgq` that contradicts its flags. -/
local macro "cas_absurd" : tactic => `(tactic| (
  simp at heq
  simp [CondCode.interp, StatusFlags.from_result] at cn
  first | exact absurd heq cn | exact absurd cn heq | simp [heq] at cn))

set_option hygiene false in
/-- After `e_reads` and the fences up to the link: `hc`, the link's outcomes. -/
local macro "e_link" : tactic => `(tactic| (
  have hE := ((((h3.fence (fenC f4).1).fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1).fence (fenC f8).1
  have hc := (vc_e_link hL _ hE).2 old g9.1 (stepR (rmwC hc).1 (by simp [e3]) (by funext x; simp [cmpxOp64, hsi']))))

set_option maxHeartbeats 12000000 in
/-- **`enq`'s specification** (the fragment, every placement): from `E0` of
`n` with the link in `r11`, `enq` returns to the link with `n` linked. -/
theorem enq_fragXR (P : Params) (n : BitVec 64) (hL : QLocs P) :
    FragSpecEnv (SharedEnv.counted (EEX P)) enqFrag "enq" (EnqPre P n) (EnqPost P n) := by
  refine FragSpecEnv.of_cfg (enqTable P n) rfl (by decide)
    (fun ra t g ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, Saved.refl t, h4, .inl ⟨rfl, h5⟩⟩) ?_
  intro _
  rintro ra t g -
  cfg_cases_env [enqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : (_ ∧ _) ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨⟨h11, hdi, hsi, ⟨sv1, sv2, sv3, sv4, sv5, sv6, fdm⟩, hd8, hT⟩, rfl, rfl⟩ := hx
  all_goals simp only [String.reduceEq, true_and, false_and, or_false, false_or] at hT
  all_goals have hdi' := hdi; have hsi' := hsi; simp only [Reg64s.get64] at hdi' hsi'
  -- `enq`
  case vc1 | vc2 | vc3 => exact ⟨trivial, mem_sAll8 _⟩
  case vc4 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 g4 f4 cz g5 f5 _
    e_reads
    to_enq (h3.e0.fence (fenC f4).1).fence (fenC f5).1
    subst hg; fen_all; omega
  case vc5 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 g4 f4 cz g5 f5 b6 g6 f6 ct g7 f7 _
    e_reads
    simp [CondCode.interp, StatusFlags.from_result] at ct
    dsimp only
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8,
      .inr ⟨rfl, w3, w4, by simp [e3], by simp [e4], by simpa [e4] using ct,
        (((h3.fence (fenC f4).1).fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1⟩⟩,
      .inl (by decide)⟩)
    regs_kept
  case vc6 | vc9 => exact hd8 _
  case vc7 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 g4 f4 cz g5 f5 b6 g6 f6 ct g7 f7 b8 g8 f8 _
    e_reads
    have hE := ((((h3.fence (fenC f4).1).fence (fenC f5).1).fence (fenC f6).1).fence (fenC f7).1).fence (fenC f8).1
    exact okRC (okR (vc_e_link hL _ hE).1 (by simp [e3]) (by funext x; simp [cmpxOp64, hsi'])) (mem_sAll8 _)
  case vc8 =>
    rename_i old g9 hc heq cn g10 f10 _
    cas_absurd
  case vc14 | vc15 =>
    rename_i old g9 hc heq cn g10 f10 g11 f11 _
    cas_absurd
  case vc16 | vc17 =>
    rename_i old g9 hc heq cn g10 f10 g11 f11 old2 g12 hc2 heq2 g13 f13 _
    cas_absurd
  case vc10 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 g4 f4 cz g5 f5 b6 g6 f6 ct g7 f7 b8 g8 f8 old g9 hc heq cn g10 f10
      g11 f11 _
    e_reads
    e_link
    simp at heq
    rcases hc with ⟨hne, -⟩ | ⟨-, hLk⟩
    · exact absurd heq hne
    have hLk' := (hLk.fence (fenC f10).1).fence (fenC f11).1
    exact okRC (okR (vc_e_swing hL _ hLk').1 (by simp [hdi', Params.tail])
      (by funext x; simp [cmpxOp64, e3, hsi'])) (mem_sAll8 _)
  case vc11 | vc12 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 g4 f4 cz g5 f5 b6 g6 f6 ct g7 f7 b8 g8 f8 old g9 hc heq cn g10 f10
      g11 f11 old2 g12 hc2 heq2 g13 f13 _
    e_reads
    e_link
    simp at heq
    rcases hc with ⟨hne, -⟩ | ⟨-, hLk⟩
    · exact absurd heq hne
    have hLk' := (hLk.fence (fenC f10).1).fence (fenC f11).1
    have hs := (vc_e_swing hL _ hLk').2 old2 g12.1 (stepR (rmwC hc2).1 (by simp [hdi', Params.tail])
      (by funext x; simp [cmpxOp64, e3, hsi']))
    refine .inr ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, _, hs.fence (fenC f13).1⟩
    regs_kept
  case vc13 =>
    rename_i v3 g1 ld1 v4 g2 ld2 v5 g3 ld3 g4 f4 cz g5 f5 b6 g6 f6 ct g7 f7 b8 g8 f8 old g9 hc heq cn g10 f10 _
    e_reads
    e_link
    simp at heq
    rcases hc with ⟨-, hE0⟩ | ⟨hz, -⟩
    · to_enq hE0.fence (fenC f10).1
      subst hg; fen_all; omega
    · exact absurd hz heq
  -- `enq_swing`
  case vc1 => exact hd8 _
  case vc2 =>
    rename_i g1 f1 _
    obtain ⟨y3, y4, hb, hcx, hnz, h2⟩ := hT
    have hcx' := hcx; have hb' := hb; simp only [Reg64s.get64] at hcx' hb'
    exact okRC (okR (vc_e_help hL _ (h2.fence (fenC f1).1) hnz).1 (by simp [hdi', Params.tail])
      (by funext x; simp [cmpxOp64, hb', hcx'])) (mem_sAll8 _)
  case vc3 | vc4 =>
    rename_i g1 f1 old g2 hc heq g3 f3 _
    obtain ⟨y3, y4, hb, hcx, hnz, h2⟩ := hT
    have hcx' := hcx; have hb' := hb; simp only [Reg64s.get64] at hcx' hb'
    have hE := (vc_e_help hL _ (h2.fence (fenC f1).1) hnz).2 old g2.1
      (stepR (rmwC hc).1 (by simp [hdi', Params.tail]) (by funext x; simp [cmpxOp64, hb', hcx']))
    to_enq hE.fence (fenC f3).1
    subst hg; fen_all; omega

/-! ## `deq` -/

/-- **`Kept`**: `g`'s first-dequeue records persist (`deq`'s relational frame). -/
def Kept (P : Params) (g : EStateX) : EStateX → Prop := fun σ => ∀ x0, First P x0 g → First P x0 σ

/-- `deq`'s precondition: link `ra`, `rdi = &head`, `rsi = &tail`, `ComD`. -/
def DeqPre (P : Params) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (EDX P)).State) : Prop :=
  t.regs.get64 .r11 = ra.toBitVec ∧ t.regs.get64 .rdi = P.h ∧ t.regs.get64 .rsi = P.t ∧ D8 t.dmem ∧ ComD P σ.1

/-- `deq`'s postcondition: the frame kept, `ComD`, the result `rax` recorded
as a first dequeue (`First`), and **relationally**: after any dequeue `x0`
recorded at the entry, `x0` then `rax` (`DoneD2`). -/
def DeqPost (P : Params) (_ : Int64) (t : MachineData) (g : (SharedEnv.counted (EDX P)).State)
    (s : MachineData) (σ : (SharedEnv.counted (EDX P)).State) : Prop :=
  Saved t s ∧ ComD P σ.1 ∧ First P (s.regs.get64 .rax) σ.1 ∧
    ∀ x0, First P x0 g.1 → DoneD2 σ.1.snap.mem P x0 (s.regs.get64 .rax)

/-- `deq`'s table: `ComD ∧ Kept` at `deq`; at `deq_pop` the three reads
(`D3`) with `head ≠ tail`. -/
abbrev deqTable (P : Params) (ra : Int64) (t : MachineData) (g : (SharedEnv.counted (EDX P)).State) :
    Label → MachineData → (SharedEnv.counted (EDX P)).State → Prop :=
  fun lb s σ => s.regs.get64 .r11 = ra.toBitVec ∧ s.regs.get64 .rdi = P.h ∧ s.regs.get64 .rsi = P.t ∧
    Saved t s ∧ D8 s.dmem ∧
    ((lb = "deq" ∧ ComD P σ.1 ∧ Kept P g.1 σ.1) ∨
      (lb = "deq_pop" ∧ ∃ y3 yt u, s.regs.get64 .rdx = BitVec.setWidth 64 y3 ∧
        s.regs.get64 .rcx = BitVec.setWidth 64 u ∧ BitVec.setWidth 64 yt ≠ BitVec.setWidth 64 y3 ∧
        D3 P (Kept P g.1) y3 yt u σ.1))

/-- `Kept` is a frame of the dequeuer's VCs. -/
theorem yok_kept (P : Params) (g : EStateX) : YOk P (Kept P g) where
  fence h hf x0 hx := (yok_first x0).fence (h x0 hx) hf
  load h hf x0 hx := (yok_first x0).load (h x0 hx) hf
  rmw h hs x0 hx := (yok_first x0).rmw (h x0 hx) hs

/-- `h` through the fences `fs` (with the frame `Kept`). -/
local macro "kf% " h:term:max " [" fs:ident,* "]" : term => do
  let mut acc : Lean.Term := h
  for f in fs.getElems do acc ← `(($acc).fence (yok_kept _ _) (fenC $f).1)
  return acc

set_option hygiene false in
/-- `deq`'s four reads: `h4 : D3` after them. -/
local macro "d_reads" : tactic => `(tactic| (
  obtain ⟨w3, hs1, c1, e3⟩ := ldC hd8 ld1
  have h1 := vc_d_load_head (yok_kept _ _) _ hT.1 hT.2 w3 g1.1 (stepL hs1 (by simp [hdi', Params.head]))
  obtain ⟨wt, hs2, c2, e4⟩ := ldC hd8 ld2
  have h2 := vc_d_load_tail (yok_kept _ _) _ h1 wt g2.1 (stepL hs2 (by simp [hsi', Params.tail]))
  obtain ⟨wu, hs3, c3, e5⟩ := ldC hd8 ld3
  have h3 := vc_d_load_link (yok_kept _ _) _ h2 wu g3.1 (stepL hs3 (by simp [e3]))
  obtain ⟨w6, hs4, c4, -⟩ := ldC hd8 ld4
  have h4 := vc_d_load3 (yok_kept _ _) _ h3 w6 g4.1 hs4))

set_option hygiene false in
/-- Land at `deq` with `ComD ∧ Kept` `t` (a back edge). -/
local macro "to_deq" t:term : tactic => `(tactic| (
  dsimp only
  refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8,
    .inl ⟨rfl, ($t).1, ($t).2⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
  regs_kept))

set_option hygiene false in
/-- At `deq_pop`, the swing: `hD1 : D3` before it, `hP` its outcome. -/
local macro "p_pop0" : tactic => `(tactic| (
  obtain ⟨y3, yt, u, hb, hcx, hne, hD⟩ := hT
  have hb' := hb; have hcx' := hcx; simp only [Reg64s.get64] at hb' hcx'
  have hD1 := hD.fence (yok_kept _ _) (fenC f1).1
  have hP := (vc_d_pop hL hpt (yok_kept _ _) _ hD1 hne).2 old g2.1
    (stepR (rmwC hc).1 (by simp [hdi', Params.head]) (by funext x; simp [cmpxOp64, hb', hcx']))))

set_option maxHeartbeats 12000000 in
/-- **`deq`'s specification** (the fragment, every placement): from `ComD`
with the link in `r11`, `deq` returns the dequeued node in `rax`. -/
theorem deq_fragXR (P : Params) (hL : QLocs P) (hpt : P.trk = false) :
    FragSpecEnv (SharedEnv.counted (EDX P)) deqFrag "deq" (DeqPre P) (DeqPost P) := by
  refine FragSpecEnv.of_cfg (deqTable P) rfl (by decide)
    (fun ra t g ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, Saved.refl t, h4, .inl ⟨rfl, h5, fun _ h => h⟩⟩) ?_
  intro _
  rintro ra t g -
  cfg_cases_env [deqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : (_ ∧ _) ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨⟨h11, hdi, hsi, ⟨sv1, sv2, sv3, sv4, sv5, sv6, fdm⟩, hd8, hT⟩, rfl, rfl⟩ := hx
  all_goals simp only [String.reduceEq, true_and, false_and, or_false, false_or] at hT
  all_goals have hdi' := hdi; have hsi' := hsi; simp only [Reg64s.get64] at hdi' hsi'
  -- `deq`
  case vc1 | vc2 | vc3 | vc4 => exact ⟨trivial, mem_sAll8 _⟩
  case vc5 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 g5 f5 cz g6 f6 _
    d_reads
    have hb := (kf% h4 [f5, f6]).back
    to_deq hb
    subst hg; fen_all; omega
  case vc6 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 g5 f5 cz g6 f6 g7 f7 cr g8 f8 _
    d_reads
    simp [CondCode.interp, StatusFlags.from_result] at cr
    dsimp only
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8,
      .inr ⟨rfl, w3, wt, wu, by simp [e3], by simp [e5], fun h => cr (by rw [e3, e4, h]; exact BitVec.sub_self _),
        kf% h4 [f5, f6, f7, f8]⟩⟩, .inl (by decide)⟩)
    regs_kept
  case vc7 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 g5 f5 cz g6 f6 g7 f7 cr g8 f8 b9 g9 f9 ct g10 f10 _
    d_reads
    have hb := (kf% h4 [f5, f6, f7, f8, f9, f10]).back
    to_deq hb
    subst hg; fen_all; omega
  case vc8 => exact hd8 _
  case vc9 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 g5 f5 cz g6 f6 g7 f7 cr g8 f8 b9 g9 f9 ct g10 f10 g11 f11 _
    d_reads
    simp [CondCode.interp, StatusFlags.from_result] at ct
    have hE := kf% h4 [f5, f6, f7, f8, f9, f10, f11]
    exact okRC (okR (vc_d_help hL (yok_kept _ _) _ hE (by rw [← e5]; exact ct)).1
      (by simp [hsi', Params.tail]) (by funext x; simp [cmpxOp64, e3, e5])) (mem_sAll8 _)
  case vc10 | vc11 =>
    rename_i v3 g1 ld1 vt g2 ld2 vu g3 ld3 vh g4 ld4 g5 f5 cz g6 f6 g7 f7 cr g8 f8 b9 g9 f9 ct g10 f10 g11 f11
      old g12 hc heq g13 f13 _
    d_reads
    simp [CondCode.interp, StatusFlags.from_result] at ct
    have hE := kf% h4 [f5, f6, f7, f8, f9, f10, f11]
    have hC := (vc_d_help hL (yok_kept _ _) _ hE (by rw [← e5]; exact ct)).2 old g12.1
      (stepR (rmwC hc).1 (by simp [hsi', Params.tail]) (by funext x; simp [cmpxOp64, e3, e5]))
    have hb : _ ∧ _ := ⟨hC.1.fence (fenC f13).1, (yok_kept _ _).fence hC.2 (fenC f13).1⟩
    to_deq hb
    subst hg; fen_all; omega
  -- `deq_pop`
  case vc1 => exact hd8 _
  case vc2 =>
    rename_i g1 f1 _
    obtain ⟨y3, yt, u, hb, hcx, hne, hD⟩ := hT
    have hb' := hb; have hcx' := hcx; simp only [Reg64s.get64] at hb' hcx'
    exact okRC (okR (vc_d_pop hL hpt (yok_kept _ _) _ (hD.fence (yok_kept _ _) (fenC f1).1) hne).1
      (by simp [hdi', Params.head]) (by funext x; simp [cmpxOp64, hb', hcx'])) (mem_sAll8 _)
  case vc3 =>
    rename_i old g2 hc heq cn g3 f3 _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at cn
    exact absurd (by rw [heq]; exact BitVec.sub_self _) cn
  case vc6 =>
    rename_i old g2 hc heq cn g3 f3 g4 f4 g5 f5 _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at cn
    exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero cn).symm heq
  case vc4 =>
    rename_i g1 f1 old g2 hc heq cn g3 f3 g4 f4 g5 f5 _
    p_pop0
    simp at heq
    have heq' : BitVec.setWidth 64 old = BitVec.setWidth 64 y3 := heq.trans hb'
    have hF := (hP.2.2 heq')
    refine .inr ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_, ?_, ?_⟩
    regs_kept
    · exact ((hP.1.fence (fenC f3).1).fence (fenC f4).1).fence (fenC f5).1
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx]
      exact (yok_first _).fence ((yok_first _).fence ((yok_first _).fence hF.1 (fenC f3).1) (fenC f4).1)
        (fenC f5).1
    · intro x0 hx0
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx]
      have := hF.2 x0 (hD1.2.1 x0 hx0)
      rw [(fenC f5).1.snap, (fenC f4).1.snap, (fenC f3).1.snap]
      exact this
  case vc5 =>
    rename_i g1 f1 old g2 hc heq cn g3 f3 _
    p_pop0
    have hb : _ ∧ _ := ⟨hP.1.fence (fenC f3).1, (yok_kept _ _).fence hP.2.1 (fenC f3).1⟩
    to_deq hb
    subst hg; fen_all; omega

end Kraken.Promising.Lower.MsqXR
