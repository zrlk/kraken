/-
Part 10: **the data word of `treiber2.kl`**: its
final law and its two extra VCs, on top of `treiber2_nodes`
(`EnvG/Treiber2Final.lean`, `EnvG/Treiber2VC.lean`).

`treiber2.kl` adds, per thread `w`, `str w9, [x1]` (the data word `dd w` of
node `w`) before the push and `ldr w11, [x2]` (the popped node's data word)
after a successful pop. The data word is frozen with the link at the push
(`PushF`'s `D w d`), so:

- **final law** (`final_values_data`): with `DoneRD` (a pop with its data
  read `DonePopD`, or an empty stack) for both threads, each thread's `X11`
  is the data word of the node it popped: `slot_read` at the push form's
  data word, the read's window covering the push by `hist_time` (a pop of
  the other node reads at or after its push) or by `Pw ≤ tr0` (its own);
- **VCs**: `vc_data_str` (`str w9, [x1]` at `Pu0`: the data word's maximal
  write becomes `(d, tw)`, `tw ≤ vwOld`, giving `Pu`'s `DataOK`) and
  `vc_ldr_data` (`ldr w11, [x2]` after the pop at `DnB`: its window covers
  the pop's `ldar` read, `DnD`); `vc_pop_cbz_d` (the empty stack at `DnD`).
-/
import Kraken.Promising.SLR.EnvG.Treiber2VC

namespace Kraken.Promising.SLR.EnvG.Treiber2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.Treiber (initVal_eq get?_of_anchor)

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The final law -/

/-- **A pop with its data read**: `DonePopAt`, and the `ldr` of `[v]`
(4 bytes) read `u` (`x11` its zero-extended 32 bits) with no write to `[v]`
after it up to the `ldar` read `tr0`. -/
def DonePopD (P : Params) (w : Nat) (m : Memory) (v x11 : BitVec 64) : Prop :=
  ∃ Pw tr0, DonePopAt P w m v Pw tr0 ∧ ∃ tl u, m.read? ⟨v, 4⟩ tl = some u ∧
    BitVec.setWidth 64 (BitVec.setWidth 32 u) = x11 ∧
    ∀ p wm, tl < p → p ≤ tr0 → m.get? p = some wm → wm.loc ≠ ⟨v, 4⟩

/-- **Thread `w` done** (`DoneR` with the pop's data read). -/
def DoneRD (P : Params) (w : Nat) (m : Memory) (R : Res) (v x11 : BitVec 64) : Prop :=
  1 ≤ R.acq P.top w ∧ m.initVal P.top = 0 ∧ (DonePopD P w m v x11 ∨ DoneCbz P w m R)

theorem rawSide_of_doneD {P : Params} {w : Nat} {m : Memory} {R : Res} {v x : BitVec 64}
    (h : DonePopD P w m v x ∨ DoneCbz P w m R) : ∃ X, RawSide P w m R X ∧ (X.popped → X.v = v ∧
      ∃ tl u, m.read? ⟨v, 4⟩ tl = some u ∧ BitVec.setWidth 64 (BitVec.setWidth 32 u) = x ∧
        ∀ p wm, tl < p → p ≤ X.tr0 → m.get? p = some wm → wm.loc ≠ ⟨v, 4⟩) := by
  rcases h with ⟨Pw, tr0, ⟨tr, Q, y0, y1, x4, tl, u, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩,
    hd⟩ | ⟨hq, Pw, r, y0, h1, h2, h3, h4⟩
  · exact ⟨⟨Pw, P.n w, 0, True, Q, tr0, tr, v, x4⟩, ⟨h1, rfl, fun _ => ⟨h2, h3, h4, ⟨y0, h5, h6⟩, ⟨y1, h7, h8⟩,
      h9, h10, h11, tl, u, h12, h13, h14⟩, fun h => absurd trivial h⟩, fun _ => ⟨rfl, hd⟩⟩
  · exact ⟨⟨Pw, P.n w, 0, False, 0, 0, 0, 0, 0⟩, ⟨h1, rfl, fun h => h.elim, fun _ => ⟨hq, r, y0, h2, h3, h4⟩⟩,
      fun h => h.elim⟩

section Final

variable {I : ISA} {P : Params} {rF : Nat → Res} {g : Ghost} {TT : Nat → Prop} {c : Config I}

/-- The data word of `D`'s zero-extended 32 bits. -/
abbrev x32 (d : Val) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 d)

/-- **The values and data the two threads popped**: their `X10` are the two
nodes, and each `X11` the data word (`D`) of the node it popped. -/
theorem final_values_data (E : Erase rF g TT c) (hW : GW P g) (hL : TLocs P) (hno : ∀ ts, ¬ Outstanding c ts)
    {i0 i1 : Nat} (hi0 : i0 < c.threads.size) (hi1 : i1 < c.threads.size) {v0 v1 x0 x1 : BitVec 64}
    (h0 : DoneRD P 0 c.mem (rF i0) v0 x0) (h1 : DoneRD P 1 c.mem (rF i1) v1 x1) :
    (v0 = P.n 0 ∧ v1 = P.n 1 ∧ (∃ d, P.D 0 d ∧ x32 d = x0) ∧ ∃ d, P.D 1 d ∧ x32 d = x1) ∨
      (v0 = P.n 1 ∧ v1 = P.n 0 ∧ (∃ d, P.D 1 d ∧ x32 d = x0) ∧ ∃ d, P.D 0 d ∧ x32 d = x1) := by
  have htot : (total rF g c).acq P.top 0 = 1 := total_acq_of_ge' E hi0 h0.1
  obtain ⟨A0, hA, hAv⟩ := rawSide_of_doneD h0.2.2
  obtain ⟨B0, hB, hBv⟩ := rawSide_of_doneD h1.2.2
  obtain ⟨⟨sA, hsA, -, hpA⟩, -⟩ := forms_of_raw E hW htot hi0 hA
  obtain ⟨⟨sB, hsB, -, hpB⟩, -⟩ := forms_of_raw E hW htot hi1 hB
  obtain ⟨-, hqdA, hqeA, ⟨yA, tA, hXA, hmA, htA, trA, yA', htrA, hrA, hyA, hnA⟩, dA, sdA, hXdA, hmdA, hsdA, hDA⟩ :=
    hpA
  obtain ⟨-, hqdB, hqeB, ⟨yB, tB, hXB, hmB, htB, trB, yB', htrB, hrB, hyB, hnB⟩, dB, sdB, hXdB, hmdB, hsdB, hDB⟩ :=
    hpB
  obtain ⟨val, H⟩ := final_core (A := { A0 with y := BitVec.setWidth 64 yA })
    (B := { B0 with y := BitVec.setWidth 64 yB }) E hW hL hno hi0 hi1 htot h0.2.1 (hA.setY _) (hB.setY _) hsA hsB
    hqdA hXA hmA htA htrA hrA hyA hnA rfl hqdB hXB hmB htB htrB hrB hyB hnB rfl
  obtain ⟨hpa, hpb, hv⟩ := hist_ok H
  obtain ⟨e0, tl0, u0, hr0, hx0, hw0⟩ := hAv hpa
  obtain ⟨e1, tl1, u1, hr1, hx1, hw1⟩ := hBv hpb
  have hpA' := (hA.pop hpa).1
  have hpB' := (hB.pop hpb).1
  have nA : A0.n = P.n 0 := hA.n
  have nB : B0.n = P.n 1 := hB.n
  -- a data read of node `w'` whose window reaches its push reads its data
  have rd : ∀ {w' : Nat} {s : Slot} {d : Val} {sd tl tr0 : Time} {u : Val} {v : BitVec 64}, s ∈ g.u →
      (s.res.wr (P.dd w')).q = 1 → (s.res.wr (P.dd w')).X (d, sd) → (∀ p, (s.res.wr (P.dd w')).X p → p.2 ≤ sd) →
      v = P.n w' → c.mem.read? ⟨v, 4⟩ tl = some u →
      (∀ p wm, tl < p → p ≤ tr0 → c.mem.get? p = some wm → wm.loc ≠ ⟨v, 4⟩) → sd ≤ tr0 → u = d := by
    intro w' s d sd tl tr0 u v hs hq hX hm hv hr hw hle
    subst hv
    exact slot_read E hno hs hq hX hm hr hw hle
  rcases hv with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have ha' : v0 = P.n 0 := by rw [← e0, ← nA]; exact ha
    have hb' : v1 = P.n 1 := by rw [← e1, ← nB]; exact hb
    refine .inl ⟨ha', hb', ⟨dA, hDA, ?_⟩, dB, hDB, ?_⟩
    · rw [← rd hsA hqeA hXdA hmdA ha' hr0 hw0 (by omega_t)]; exact hx0
    · rw [← rd hsB hqeB hXdB hmdB hb' hr1 hw1 (by omega_t)]; exact hx1
  · have ha' : v0 = P.n 1 := by rw [← e0, ← nB]; exact ha
    have hb' : v1 = P.n 0 := by rw [← e1, ← nA]; exact hb
    have t0 : B0.p ≤ A0.tr0 := by have := hist_time H hpa ha; exact this
    have t1 : A0.p ≤ B0.tr0 := by have := hist_time H.swap hpb hb; exact this
    refine .inr ⟨ha', hb', ⟨dB, hDB, ?_⟩, dA, hDA, ?_⟩
    · rw [← rd hsB hqeB hXdB hmdB ha' hr0 hw0 (by omega_t)]; exact hx0
    · rw [← rd hsA hqeA hXdA hmdA hb' hr1 hw1 (by omega_t)]; exact hx1

end Final

/-! ## The table predicates and the VCs -/

/-- **`worker`** (before `str w9, [x1]`): `Pu` without `DataOK`, the data
word whole with its writes at or below `coh`. -/
def Pu0 (P : Params) (w : Nat) (σ : State isa) : Prop :=
  Com P w σ ∧ ¬ Pushed P σ.r ∧ (σ.r.wr (P.nd w)).q = 1 ∧
    (∀ p, (σ.r.wr (P.nd w)).X p → p.2 ≤ σ.vs.getCoh (P.nd w)) ∧ (σ.r.wr (P.dd w)).q = 1 ∧
    (∀ p, (σ.r.wr (P.dd w)).X p → p.2 ≤ σ.vs.getCoh (P.dd w)) ∧ (σ.r.wr (P.pt w)).q = 1

/-- **`done`** with `X10 = x10`, `X11 = x11`: `DonePopD` or `DoneCbz`. -/
def DnD (P : Params) (w : Nat) (x10 x11 : BitVec 64) (σ : State isa) : Prop :=
  Com P w σ ∧ (DonePopD P w σ.snap.mem x10 x11 ∨ DoneCbz P w σ.snap.mem σ.r)

section VC

variable {P : Params} {w : Nat} {σ σ' : State isa}

theorem Pu0.fence (h : Pu0 P w σ) (hf : FenceLe σ σ') : Pu0 P w σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1.fence hf, hf.r ▸ h2, hf.r ▸ h3, ?_, hf.r ▸ h5, ?_, hf.r ▸ h7⟩ <;> rw [hf.r, hf.getCoh] <;> assumption

theorem DnD.fence {x y : BitVec 64} (h : DnD P w x y σ) (hf : FenceLe σ σ') : DnD P w x y σ' := by
  unfold DnD; rw [hf.snap, hf.r]; exact ⟨h.1.fence hf, h.2⟩

/-- **VC `str w9, [x1]`** (the data word, a value `v` with `D w v`):
permitted (pure, the word whole), and `Pu` after it. -/
theorem vc_data_str (σ : State isa) (h : Pu0 P w σ) (v : Val) (hD : P.D w v) :
    (EW P w).ok (.store .plain false (P.dd w).addr (P.dd w).bytes v) σ ∧
      ∀ b (σ' : State isa), (EW P w).step (.store .plain false (P.dd w).addr (P.dd w).bytes v) σ b σ' →
        Pu P w σ' := by
  obtain ⟨⟨hW, hpos, hacq, hi, hfw⟩, hnp, hq, hX, hqd, hXd, hpt⟩ := h
  have e : ({ addr := (P.dd w).addr, bytes := (P.dd w).bytes } : Loc) = P.dd w := rfl
  have hne : P.dd w ≠ P.top := Ne.symm (top_dd P w)
  refine ⟨⟨rfl, by rw [e, hqd]; decide, fun _ => by rw [e, hW.rel_ne hne]; exact Pred.emp_pure _,
    fun hr => by rw [e, plan_rel] at hr; simp [hne] at hr⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, hws, hwb, hwv, -, ⟨_, -, hr⟩, -, -⟩ := step_storeFacts (pl := plan P w) hs
  rw [e, plan_after_ne P w hne] at hr
  have hwr : ∀ x, x ≠ P.dd w → σ'.r.wr x = σ.r.wr x := fun x hx => by rw [hr, Res.addW_wr_ne _ _ hx]
  refine ⟨⟨hW.mono hanc.ghost, by rw [hwr _ (Ne.symm hne)]; exact hpos, by rw [hr, Res.addW_acq]; exact hacq,
    ?_, fun f hf => ?_⟩, ?_, by rw [hwr _ (nd_dd P w w)]; exact hq, fun p hp => ?_,
    ⟨by rw [hr, Res.addW_q]; exact hqd, v, tw, ?_, ?_, hwv.vwOld (by decide), hD⟩,
    by rw [hwr _ (Ne.symm (dd_pt P w w))]; exact hpt⟩
  · rw [initVal_eq (Treiber.WriteSnap.init hws), initVal_eq hanc.snap.init]; exact hi
  · rw [hwv.fwdOther _ (Ne.symm hne)] at hf
    exact Nat.le_trans (hfw f hf) hwv.mono.vrNew
  · unfold Pushed; rw [hwr _ (Ne.symm hne)]; exact hnp
  · rw [hwr _ (nd_dd P w w)] at hp
    exact Nat.le_trans (hX p hp) (hwv.mono.coh _)
  · rw [hr, Res.addW_X_self]; exact .inr ⟨by rw [hqd]; decide, rfl⟩
  · intro p hp
    rw [hr, Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hXd p hp) hwb.coh)
    · exact Nat.le_refl _

/-- **VC `ldr w11, [x2]`** after a successful pop (`x2 = x` the node): its
window covers the pop's `ldar` read (`DnD`). -/
theorem vc_ldr_data (σ : State isa) {x : BitVec 64} (h : DnB P w x σ) {xcl : Bool} :
    ∀ u (σ' : State isa), (EW P w).step (.load .plain xcl x 4) σ u σ' → DnD P w x (x32 u) σ' := by
  intro u σ' hs
  have hf := step_loadFacts (pl := plan P w) hs
  obtain ⟨hcom, Pw, tr0, hle, hd⟩ := h
  refine ⟨hcom.load hf, .inl ⟨Pw, tr0, ?_⟩⟩
  obtain ⟨hanc, -, -, tl, hrd, hlv, -⟩ := hf
  refine ⟨hd.mono (AnchorOk.prefix hanc), tl, u, hrd.val, rfl, fun p wm a b hg hl => ?_⟩
  have := (Memory.writeIn_iff _ _ _ _).mpr ⟨p, wm, a, Nat.le_trans b (Nat.le_trans hle
    (le_readBound_vrNew Arch.armv8 σ.vs .plain ⟨x, 4⟩)), hg, hl⟩
  rw [hrd.window] at this; cases this

/-- **`cbz x2, done` taken** (`DnD`, any `X11`). -/
theorem vc_pop_cbz_d (σ : State isa) {y0 : Val} (h : Pl P w y0 σ) (hz : BitVec.setWidth 64 y0 = 0)
    (x y : BitVec 64) : DnD P w x y σ := by
  obtain ⟨hcom, Pw, tr0, ⟨h1, -, -, h4⟩, h5, h6, -⟩ := h
  exact ⟨hcom, .inr ⟨h4, Pw, tr0, y0, h1, h5, h6, hz⟩⟩

end VC

end Kraken.Promising.SLR.EnvG.Treiber2
