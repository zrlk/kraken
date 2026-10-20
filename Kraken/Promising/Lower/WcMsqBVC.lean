/-
**WeakCore's `deq` at dequeuer thread `k`**
(shape B). Shape A's VCs (`WcMsqVC`, thread `1`, `ComD2`,
writer `1`) at any `k` on MsQueue3's `ED3 P k`/`ComD3 P k` (thread `2` holds
`tokD2`), recording the own swing of writer `k` (`DoneK`). `bdeq_spec`: `deq`
in `progD1`, result tag `1` (empty) or tag `0` with `DoneK … k x1`.
-/
import Kraken.Promising.Lower.WcMsqSpecs
import Kraken.Promising.SLR.EnvG.MsQueue3VC

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.WcMsq

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.SLR.EnvG.Treiber (casOp64 casOp64_some casOp64_none)
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_mono prefix_append)
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem)

variable {P : Params2} {k : Nat}

/-- After the plain link read (`DQ3w` at thread `k`). -/
def DQ3k (P : Params2) (k : Nat) (y3 y5 : Val) (σ : State isa) : Prop :=
  ComD3 P k σ ∧ ∃ a tr0, σ.snap.mem.read? P.head a = some y3 ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0 = some y5 ∧ (tr0 ≤ σ.vs.vrOld ∨ tr0 ≤ σ.vs.vrNew)

/-- After the successful `casal`: the reads, and the own swing (writer `k`). -/
def SwK (P : Params2) (k : Nat) (y3 y5 : Val) (σ : State isa) : Prop :=
  ComD3 P k σ ∧ ∃ a tr0 tw vh, σ.snap.mem.read? P.head a = some y3 ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0 = some y5 ∧ BitVec.setWidth 64 y5 ≠ 0 ∧
    tr0 ≤ σ.vs.vrNew ∧ σ.snap.mem.get? tw = some ⟨P.head, vh, k⟩ ∧ BitVec.setWidth 64 vh = BitVec.setWidth 64 y5

theorem DQ3k.fence {y3 y5 : Val} {σ σ' : State isa} (h : DQ3k P k y3 y5 σ) (hf : FenceLe σ σ') :
    DQ3k P k y3 y5 σ' := by
  obtain ⟨h1, a, tr0, h2, h3, h4⟩ := h
  have hro : σ'.vs.vrOld = σ.vs.vrOld := by rw [hf.vs]
  exact ⟨h1.fence hf, a, tr0, hf.snap ▸ h2, hf.snap ▸ h3, h4.imp (fun h => hro ▸ h) fun h => Nat.le_trans h hf.vrNew⟩

theorem SwK.fence {y3 y5 : Val} {σ σ' : State isa} (h : SwK P k y3 y5 σ) (hf : FenceLe σ σ') : SwK P k y3 y5 σ' :=
  let ⟨h1, a, tr0, tw, vh, h2, h3, h4, h5, h6, h7⟩ := h
  ⟨h1.fence hf, a, tr0, tw, vh, hf.snap ▸ h2, hf.snap ▸ h3, h4, Nat.le_trans h5 hf.vrNew, hf.snap ▸ h6, h7⟩

/-- **VC `ldr x3, [x0]`**: `head` read. -/
theorem vcB_head (σ : State isa) (h : ComD3 P k σ) {kl : LoadKind} {xcl : Bool} :
    ∀ v (σ' : State isa), (ED3 P k).step (.load kl xcl P.head.addr P.head.bytes) σ v σ' → DQ1' P k v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  refine ⟨h.load hf, ?_⟩
  obtain ⟨-, -, -, tr, hrd, -⟩ := hf
  exact ⟨tr, hrd.val⟩

/-- **VC `ldr x5, [x8]`**: the link read, plain (`vc_d_ldr_link` at `k`). -/
theorem vcB_link (σ : State isa) {y3 : Val} (h : DQ1' P k y3 σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (ED3 P k).step (.load .plain xcl (BitVec.setWidth 64 y3 + 8) 8) σ v σ' →
      DQ3k P k y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  obtain ⟨hc, a, ha⟩ := h
  refine ⟨hc.load hf, a, ?_⟩
  obtain ⟨hanc, -, -, tr0, hrd, hlv, -⟩ := hf
  refine ⟨tr0, hanc.read? ha, hrd.val, ?_⟩
  by_cases hfw : Fwded σ.vs ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0
  · obtain ⟨f, hf, rfl⟩ := hfw
    exact .inr (Nat.le_trans (hc.2.2.2.2.2 _ f hf) hlv.mono.vrNew)
  · exact .inl (hlv.vrOld hfw)

/-- **VC `casal x6, x5, [x0]`** (`vc_d_casw` at `k`): permitted; then `SwK`. -/
theorem vcB_cas (hL : QLocs2 P) (σ : State isa) {y3 y5 : Val} (h : DQ3k P k y3 y5 σ)
    (hnz : BitVec.setWidth 64 y5 ≠ 0) :
    (ED3 P k).ok (.rmw .acqRel P.head.addr P.head.bytes
        (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ ∧
      ∀ old (σ' : State isa), (ED3 P k).step (.rmw .acqRel P.head.addr P.head.bytes
          (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ old σ' →
        ComD3 P k σ' ∧ (BitVec.setWidth 64 old = BitVec.setWidth 64 y3 → SwK P k y3 y5 σ') := by
  obtain ⟨hc, a, tr0, h1, h2, h3⟩ := h
  have hW := hc.1
  have e : ({ addr := P.head.addr, bytes := P.head.bytes } : Loc) = P.head := rfl
  have hq : P.IsW P.head := .inl rfl
  refine ⟨⟨hc.2.1, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => ?_⟩
  · rw [e, planD2_rel] at hr; simp [hq] at hr
  · rw [e]; exact hW.impure hq new
  · rw [e, planD2_gives]; simp
  · obtain ⟨ho, rfl⟩ := casOp64_some hon
    rw [e, hW.rel_w hq]
    obtain ⟨rF, E⟩ := hanc.erase
    refine form2_ht hL _ (.inl rfl) (fun _ => ?_) fun hx => absurd hx hL.q1.head_tail
    obtain ⟨hb, h2'⟩ := read_at_append hanc h2 ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 y5), k⟩
    exact ⟨by simpa using hnz, tr, old, tr0, y5, htr, read?_mono (prefix_append _ _) hrd.val,
      noMsgIn_of_adj (hW.mono hanc.ghost) E hq hadj _, hb, by rw [ho]; exact h2', by simp⟩
  have hs' := envGCAdj_step_iff.mp hs
  refine ⟨hc.rmw hs', fun heq => ?_⟩
  obtain ⟨c, tr, hanc, -, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon, -⟩ | ⟨new, tw, hon, -, -, hws, hwb, hcoh, -, -, -, -⟩
  · exact absurd heq (casOp64_none hon)
  have hvr := rmw_acqRel_coh_le_vrNew hs' hon
  obtain ⟨-, rfl⟩ := casOp64_some hon
  have hrel := hwb.rel (by decide)
  have hpre := rmw_snap_prefix hs'
  refine ⟨hc.rmw hs', a, tr0, tw, _, read?_mono hpre h1, read?_mono hpre h2, hnz, ?_,
    Treiber.WriteSnap.get?_new hws, by simp⟩
  rcases h3 with h3 | h3
  · have : σ.vs.vrOld < tw :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hrel
    exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt h3 this)) (Nat.le_trans hcoh hvr)
  · exact Nat.le_trans h3 hvle.vrNew

/-- **VC `ldr w1, [x5]`** (the payload, after the swing): `DoneK … k`. -/
theorem vcB_payload (σ : State isa) {y3 y5 : Val} (h : SwK P k y3 y5 σ) {xcl : Bool} :
    ∀ u (σ' : State isa), (ED3 P k).step (.load .plain xcl (BitVec.setWidth 64 y5) 4) σ u σ' →
      ComD3 P k σ' ∧ DoneK σ'.snap.mem P k (BitVec.setWidth 64 (BitVec.setWidth 32 u)) := by
  intro u σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  obtain ⟨hc, a, tr0, tw, vh, h1, h2, hnz, h3, hg, hvh⟩ := h
  refine ⟨hc.load hf, ?_⟩
  obtain ⟨hanc, -, -, tl, hrd, hlv, -⟩ := hf
  refine ⟨tw, y3, y5, vh, ⟨a, tr0, tl, u, hanc.read? h1, hanc.read? h2, hnz, hrd.val, fun p wm ha hb hg hl => ?_,
    rfl⟩, Memory.get?_of_prefix (Treiber2.AnchorOk.prefix hanc).2 hg, hvh⟩
  have := (Memory.writeIn_iff _ _ _ _).mpr ⟨p, wm, ha, Nat.le_trans hb (Nat.le_trans h3
    (le_readBound_vrNew Arch.armv8 σ.vs .plain ⟨BitVec.setWidth 64 y5, 4⟩)), hg, hl⟩
  rw [hrd.window] at this; cases this

set_option mvcgen.warning false
set_option experimental.vcgen true

section Deq

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progD1)]

local instance progD1.env : CodeEnv := ⟨layout progD1⟩

theorem progD1_placed : Program.Placed progD1 "main_d1" := Program.placed_of_layout (by decide) rfl (by decide)

/-- `deq`'s precondition at thread `k`. -/
def BPre (P : Params2) (k : Nat) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (ED3 P k)).State) : Prop :=
  t.lr = ra ∧ t.regs.X0.toBitVec = P.h ∧ NoDmem t ∧ ComD3 P k σ.1

/-- `deq`'s postcondition: frame, `ComD3`, tag `1` or tag `0` with `DoneK`. -/
def BPost (P : Params2) (k : Nat) (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (ED3 P k)).State)
    (t' : MachineData) (σ' : (SharedEnv.counted (ED3 P k)).State) : Prop :=
  CalleeSaved t t' ∧ ComD3 P k σ'.1 ∧
    (t'.regs.X0.toBitVec = 1 ∨ (t'.regs.X0.toBitVec = 0 ∧ DoneK σ'.1.snap.mem P k t'.regs.X1.toBitVec))

set_option hygiene false in
local macro "b_reads" : tactic => `(tactic| (
  simp [hd8] at hld1 hld2
  obtain ⟨u3, hu3, rfl⟩ := hld1
  obtain ⟨u5, hu5, rfl⟩ := hld2
  rw [hx0] at hu3
  have h1 := (vcB_head _ hC u3 σ1.1 hu3.1).fence hf1.1
  have h3 := (vcB_link _ h1 u5 σ3.1 hu5.1).fence hf2.1))

/-- **WeakCore's `deq` at thread `k`, specified** (in `progD1`). -/
theorem bdeq_spec (P : Params2) (hL : QLocs2 P) (k : Nat) :
    FunSpecPartialEnv (SharedEnv.counted (ED3 P k)) ((_root_.Executable.labels cenv).label "deq") (BPre P k)
      (BPost P k) := by
  rintro ra t g ⟨hlr, hx0, ⟨hd8, hd4⟩, hC⟩
  refine cfgEnv_partial_fun (p := wcDeqFrag) (fun lb s σ => s.regs.X0.toBitVec = P.h ∧
      (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.lr = ra ∧
      CalleeSaved t s ∧ ComD3 P k σ.1 ∧ (lb = "deq" ∨ lb = "deq_empty"))
    (E := fun a s σ => a = ra ∧ BPost P k ra t g s σ) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE progD1_placed (by decide)) t g
    ⟨hx0, hd8, hd4, hlr, by simp [CalleeSaved], hC, .inl rfl⟩
  cfg_cases_env [wcDeqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd8, hd4, hlr, hfr, hC, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hd8]; done)
  case vc5 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v5 σ3 hz σ4 hld1 hf1 hld2 hf2 _
    b_reads
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, h3.1, by decide⟩, ?_⟩)
    exact .inl (by decide)
  case vc8 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v5 σ3 hnz σ4 σ5 hld1 hf1 hld2 hf2 hf3 _
    b_reads
    simp at hnz
    have h := (vcB_cas hL _ (h3.fence hf3.1) hnz).1
    simp [hx0]
    simpa [casOp64, Params.head] using h
  case vc9 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v5 σ3 hnz σ4 σ5 old σ6 σ7 hne σ8 hld1 hf1 hld2 hf2 hf3 hcas hf4 hf5 _
    b_reads
    simp at hnz
    have hc := (vcB_cas hL _ (h3.fence hf3.1) hnz).2 old σ6.1 (by simpa [hx0, casOp64, Params.head] using hcas.1)
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, (hc.1.fence hf4.1).fence hf5.1,
      by decide⟩, ?_⟩)
    refine .inr fun ⟨_, hg⟩ => ?_
    subst hg
    have e1 := hu3.2; have e2 := hu5.2; have e3 := hcas.2; have e4 := hf1.2; have e5 := hf2.2
    have e6 := hf3.2; have e7 := hf4.2; have e8 := hf5.2
    simp only [SharedEnv.tick_rmw] at e3
    omega
  case vc12 =>
    rename_i s σ0 r1 v3 σ1 σ2 r2 v5 σ3 hnz σ4 σ5 old σ6 σ7 heq σ8 r3 u σ9 σ10 σ11 hld1 hf1 hld2 hf2 hf3 hcas
      hf4 hf5 hld3 hf6 hf7 _
    b_reads
    simp at hnz
    have hc := (vcB_cas hL _ (h3.fence hf3.1) hnz).2 old σ6.1 (by simpa [hx0, casOp64, Params.head] using hcas.1)
    simp at heq
    have hsw := ((hc.2 (TreiberCommon.bv64_eq_of_sub_eq_zero heq)).fence hf4.1).fence hf5.1
    simp [hd4] at hld3
    obtain ⟨u1, hu1, rfl⟩ := hld3
    have hp := vcB_payload _ hsw u1 σ9.1 hu1.1
    refine .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr,
      (hp.1.fence hf6.1).fence hf7.1, .inr ⟨by simp, ?_⟩⟩
    simpa [hf6.1.snap, hf7.1.snap] using hp.2
  case vc1 =>
    rename_i s σ0 σ1 σ2 hf1 hf2 _
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr,
      (hC.fence hf1.1).fence hf2.1, .inl (by simp)⟩
  all_goals done

end Deq

end Kraken.Promising.Lower.WcMsq
