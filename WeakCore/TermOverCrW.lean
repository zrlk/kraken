import WeakCore.TermOverCr5
import WeakCore.TermIall

/-! # TermOverCrW: the window guard along frame steps (plantOpG replacement)

`WinG` (`PlantOpG`'s (A)+(B) at a bound, at the unit (F3)) guards the cover conjunct of `OverCrL`.  Along a step
that keeps memory's prefix, adds promises only above the old memory, lowers no coherence and
drops no footprint promise at `l`, a post-step guard holds before (`winG_back`), as
`overCr_frame`'s `hG` needs.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem lt_size_of_some {s : St} {t : Ts} {m : Msg} (h : s.mem[t]? = some m) : t < s.mem.size := by
  by_cases ht : t < s.mem.size
  · exact ht
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt ht)] at h
    exact absurd h (by simp)

/-- **The guard transported back** along a frame step. -/
theorem winG_back {E E' : TEnv} {s s' : St} {l : AllocLabel} {o : Nat} {tw : Ts}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hnew : ∀ t, t ∈ s'.promises → t ∉ s.promises → s.mem.size ≤ t)
    (hcoh : ∀ a, s'.vs.coh a ≤ s.vs.coh a)
    (hfp : ∀ t, t < s.mem.size → t ∈ FpAt E ⟨l, 0⟩ → t ∈ FpAt E' ⟨l, 0⟩)
    (h : TermOverCr.WinG E' s' l o tw) : TermOverCr.WinG E s l o tw := by
  refine ⟨fun t m hm hl ht => ?_, fun t m ht hm hl => ?_⟩
  · have hsz := lt_size_of_some hm
    have hm' : s'.mem[t]? = some m := by rw [hpre t hsz]; exact hm
    rcases h.1 t m hm' hl ht with hp | hc
    · by_cases hin : t ∈ s.promises
      · exact .inl hin
      · exact absurd (hnew t hp hin) (Nat.not_le_of_lt hsz)
    · exact .inr (Nat.le_trans hc (hcoh m.loc))
  · have hsz := lt_size_of_some hm
    exact h.2 t m (hfp t hsz ht) (by rw [hpre t hsz]; exact hm) hl

#print axioms winG_back

end TermOverCrW

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- At a label with a frontier, the footprint at the label is the whole footprint. -/
theorem fp_mem_FpAt {E : TEnv} {l : AllocLabel} {t : Ts} (hpf : E.pfr l ≠ none) (ht : t ∈ E.fp) :
    t ∈ FpAt E ⟨l, 0⟩ := by
  have hv : Vis E l := fun hp => hpf hp.2
  simp only [FpAt, hv, ↓reduceIte]
  exact ht

/-- (gd_fund under the guard) **`gd_item` with its footprint premise from the window guard**:
at each `K` unit the lowest own promise meets `WinG` in `j`'s cut. -/
theorem gd_itemW {Eg : GEnv} {c : Cfg} {j k : Nat} {thj thk : TTh} {Sj Sk : AllocLabel → Prop}
    {cr : Ts → Res} {l : AllocLabel} {cl : Cell} {g : TermPiece.GdE} {tP : Ts} {mh : Msg}
    {us : List Acc} {K : Nat → Bool}
    (hP : PromsOK Eg c) (hj : c.ths[j]? = some thj) (hk : c.ths[k]? = some thk) (hsh : Eg.Shared l)
    (hpf : Eg.pfr l ≠ none)
    (hc : (Cut Eg j Sj).sto l = some cl) (hgl : g.l = l)
    (hg : TermPiece.GdOK (Cut Eg k Sk) (stOf c.mem c.pairs thk) g) (hnr : noOR g.S = true)
    (hus : accs g.S = some us)
    (hm : c.mem[tP]? = some mh) (hlab : mh.loc.label = l)
    (hlow : TermPlant.LowOwn (stOf c.mem c.pairs thj) mh.loc tP)
    (hnw : ¬ WordUnit (Cut Eg j Sj) mh.loc) (h1 : g.b ≤ mh.loc.offset) (h2 : mh.loc.offset < g.b + nWords us)
    (hR : g.R ≤ cr tP)
    (hK : ∀ i o tw', K i = true → InAcc us i o → TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, g.b + o⟩ tw' →
      g.L o = true ∧ tw' ∈ PromAt (Cut Eg j Sj) (stOf c.mem c.pairs thj) ⟨l, g.b + o⟩ ∧
      (∀ t m, tw' < t → c.mem[t]? = some m → m.loc = ⟨l, g.b + o⟩ →
        t ∈ PromAt (Cut Eg j Sj) (stOf c.mem c.pairs thj) ⟨l, g.b + o⟩) ∧
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l (g.b + o) tw') :
    TermPlant.CrItem (Cut Eg j Sj) (stOf c.mem c.pairs thj) cr l cl (tP, g.b, g.S, g.ws, g.R, K) := by
  refine TermOverCr4.gd_item hP hj hk hsh hc hgl hg hnr hus hm hlab hlow hnw h1 h2 hR
    (fun i o tw' hKi hio hl => ?_)
  obtain ⟨hL, hin, hab, hW⟩ := hK i o tw' hKi hio hl
  refine ⟨hL, hin, hab, fun t m ht hm' hl' => ?_⟩
  have hpf' : (Cut Eg j Sj).pfr l ≠ none := hpf
  exact hW.2 t m (fp_mem_FpAt hpf' ht) hm' hl'

#print axioms gd_itemW

/-- (PredCov) `gd_itemQ` with its footprint premise from the window guard. -/
theorem gd_itemWQ {Eg : GEnv} {c : Cfg} {j k : Nat} {thj thk : TTh} {Sj Sk : AllocLabel → Prop}
    {cr : Ts → Res} {l : AllocLabel} {cl : Cell} {g : TermPiece.GdE} {tP : Ts} {mh : Msg}
    {us : List Acc} {K : Nat → Bool}
    (hP : PromsOK Eg c) (hj : c.ths[j]? = some thj) (hk : c.ths[k]? = some thk) (hsh : Eg.Shared l)
    (hpf : Eg.pfr l ≠ none)
    (hc : (Cut Eg j Sj).sto l = some cl) (hgl : g.l = l)
    (hg : TermPiece.GdOK (Cut Eg k Sk) (stOf c.mem c.pairs thk) g) (hnr : noOR g.S = true)
    (hus : accs g.S = some us)
    (hm : c.mem[tP]? = some mh) (hlab : mh.loc.label = l)
    (hlow : TermPlant.LowOwn (stOf c.mem c.pairs thj) mh.loc tP)
    (hnw : ¬ WordUnit (Cut Eg j Sj) mh.loc) (h1 : g.b ≤ mh.loc.offset) (h2 : mh.loc.offset < g.b + nWords us)
    (hR : g.R ≤ cr tP)
    (hK : ∀ i o tw', K i = true → InAcc us i o → TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, g.b + o⟩ tw' →
      g.L o = true ∧ (tw' ∈ PromAt (Cut Eg j Sj) (stOf c.mem c.pairs thj) ⟨l, g.b + o⟩ ∨
        (PredU (Cut Eg j Sj) ⟨l, g.b + o⟩ ∧ FirstW c.mem ⟨l, g.b + o⟩ tw')) ∧
      (∀ t m, tw' < t → c.mem[t]? = some m → m.loc = ⟨l, g.b + o⟩ →
        t ∈ PromAt (Cut Eg j Sj) (stOf c.mem c.pairs thj) ⟨l, g.b + o⟩) ∧
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l (g.b + o) tw') :
    TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj) cr l cl (tP, g.b, g.S, g.ws, g.R, K) := by
  refine TermOverCr4.gd_itemQ hP hj hk hsh hc hgl hg hnr hus hm hlab hlow hnw h1 h2 hR
    (fun i o tw' hKi hio hl => ?_)
  obtain ⟨hL, hin, hab, hW⟩ := hK i o tw' hKi hio hl
  refine ⟨hL, hin, hab, fun t m ht hm' hl' => ?_⟩
  have hpf' : (Cut Eg j Sj).pfr l ≠ none := hpf
  exact hW.2 t m (fp_mem_FpAt hpf' ht) hm' hl'

#print axioms gd_itemWQ

end TermOverCrW

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (WA core) **No window above a seen-impossible sibling overtake**: if a unit `u1` of `l`
still has its lowest own promise `t1`, and a non-own message `f` lies above `t1` at `u1`,
then no bound `tw ≥ f` meets the window guard (the guard needs `f` seen at `u1`, while
`PromAbove` keeps coherence there below `t1`). -/
theorem winG_sibling_false {E : TEnv} {s : St} {l : AllocLabel} {u1 : Address} {t1 f tw : Ts} {mf : Msg}
    (hpa : PromAbove s) (hlow : TermPlant.LowOwn s u1 t1) (hu1 : u1.label = l)
    (hf : s.mem[f]? = some mf) (hfl : mf.loc = u1) (hf1 : t1 < f) (hfn : f ∉ s.promises) (hft : f ≤ tw)
    (hW : TermOverCr.WinG E s l u1.offset tw) : False := by
  rcases hW.1 f mf hf (by rw [hfl, ← hu1]) hft with hp | hc
  · exact hfn hp
  · obtain ⟨m1, hm1, hl1⟩ := hlow.2.1
    have h1 := hpa t1 hlow.1 m1 hm1
    rw [hl1, ← hfl] at h1
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hc (Nat.lt_trans h1 hf1))

#print axioms winG_sibling_false

end TermOverCrW

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (WA, per item) **A witness block of an item**: a run `[a0, a1)` of non-own messages (one
store) with a message above the lowest own promise of some unit of the item's piece, and a
message outside the promises at every unit of the piece. -/
def WitB (E : TEnv) (s : St) (l : AllocLabel) (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) : Prop :=
  ∃ a0 a1 usS, accs x.2.2.1 = some usS ∧ (∀ t, a0 ≤ t → t < a1 → t ∉ s.promises) ∧
    (∃ o1 t1 f1 m1, TermPlant.LowOwn s ⟨l, o1⟩ t1 ∧ a0 ≤ f1 ∧ f1 < a1 ∧ s.mem[f1]? = some m1 ∧
      m1.loc = ⟨l, o1⟩ ∧ t1 < f1) ∧
    ∀ o, x.2.1 ≤ o → o < x.2.1 + nWords usS → ∃ f2 m2, a0 ≤ f2 ∧ f2 < a1 ∧ s.mem[f2]? = some m2 ∧
      m2.loc = ⟨l, o⟩ ∧ f2 ∉ PromAt E s ⟨l, o⟩

/-- (WA) **A unit of an item's piece is not newly overtaken under the window**: with
`PromAbove`, a guarded lowest own promise `tw` at a unit of a witnessed item's piece is
already overtaken.  (F3: needs the guard at every unit of the label, i.e. the label-wide form.) -/
theorem wa_old_over {E : TEnv} {s : St} {l : AllocLabel}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} {usS : List Acc} {o : Nat} {tw : Ts}
    (hpa : PromAbove s) (hw : WitB E s l x) (hus : accs x.2.2.1 = some usS) (h1 : x.2.1 ≤ o)
    (h2 : o < x.2.1 + nWords usS) (hl : TermPlant.LowOwn s ⟨l, o⟩ tw)
    (hW : ∀ o', TermOverCr.WinG E s l o' tw) : TermPlant.OverT E s ⟨l, o⟩ tw := by
  obtain ⟨a0, a1, usS', hus', hblk, ⟨o1, t1, f1, m1, hl1, hf0, hf1, hm1, hloc1, ht1⟩, hall⟩ := hw
  rw [hus] at hus'
  cases hus'
  obtain ⟨f2, m2, hg0, hg1, hm2, hloc2, hnp⟩ := hall o h1 h2
  by_cases hlt : tw < f2
  · exact ⟨f2, m2, hlt, hm2, hloc2, hnp⟩
  · exfalso
    have hne : tw ∉ s.promises → False := fun h => h hl.1
    have ha1 : a1 ≤ tw := by
      refine Nat.le_of_not_lt fun hlt2 => hne ?_
      exact hblk tw (Nat.le_trans hg0 (Nat.le_of_not_lt hlt)) hlt2
    exact winG_sibling_false hpa hl1 rfl hm1 hloc1 ht1 (hblk f1 hf0 hf1) (Nat.le_trans (Nat.le_of_lt hf1) ha1) (hW o1)

#print axioms wa_old_over

/-- (WA, derived) **The new-cover premise of `overCr_interf`** (`hcovN`): a unit newly
overtaken at a foreign store, under the guard, lies in a new item, or in the piece of an old
item, which its witness block (`WitB`) rules out.  (F3: needs the label-wide guard, `hG`.) -/
theorem hcovN_of {E E' : TEnv} {s s' : St} {l : AllocLabel} {c : Cell} {G' : Nat → Ts → Prop}
    {Gs Gn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hpa : PromAbove s) (hG : ∀ o tw, G' o tw → ∀ o', TermOverCr.WinG E s l o' tw)
    (hwit : ∀ x ∈ Gs, WitB E s l x)
    (hnew : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw → G' o tw →
      TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      (∃ x ∈ Gn, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) ∨
      ∃ x ∈ Gs, ∃ usS, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ o < x.2.1 + nWords usS) :
    ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw → G' o tw →
      TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw ∨
      ∃ x ∈ Gn, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true := by
  intro o tw hi hv hl hg hov
  by_cases hold : TermPlant.OverT E s ⟨l, o⟩ tw
  · exact .inl hold
  · rcases hnew o tw hi hv hl hg hov hold with hn | ⟨x, hx, usS, hus, h1, h2⟩
    · exact .inr hn
    · exact absurd (wa_old_over hpa (hwit x hx) hus h1 h2 hl (hG o tw hg)) hold

#print axioms hcovN_of

/-- (WA, holder form: persistent while the item is kept) **A witness block at the holder**: a
run `[a0, a1)` of non-own indices with a message above the holder `x.1` at the holder's unit,
and an unpromised message at every unit of the piece. -/
def WitH (E : TEnv) (s : St) (l : AllocLabel) (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) : Prop :=
  ∃ a0 a1 usS mh, accs x.2.2.1 = some usS ∧ s.mem[x.1]? = some mh ∧ a1 ≤ s.mem.size ∧ (∀ t, a0 ≤ t → t < a1 → t ∉ s.promises) ∧
    (∃ f1 m1, a0 ≤ f1 ∧ f1 < a1 ∧ s.mem[f1]? = some m1 ∧ m1.loc = mh.loc ∧ x.1 < f1) ∧
    ∀ o, x.2.1 ≤ o → o < x.2.1 + nWords usS → ∃ f2 m2, a0 ≤ f2 ∧ f2 < a1 ∧ s.mem[f2]? = some m2 ∧
      m2.loc = ⟨l, o⟩ ∧ f2 ∉ PromAt E s ⟨l, o⟩

/-- The holder form gives the witness block (the holder is the item's lowest own promise). -/
theorem witB_of_witH {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)}
    (hit : TermOverCr.CrItemQ E s cr l c x) (hw : WitH E s l x) : WitB E s l x := by
  obtain ⟨mh0, -, hmh0, hlab, hlo, -⟩ := hit
  obtain ⟨a0, a1, usS, mh, hus, hmh, -, hblk, ⟨f1, m1, hf0, hf1, hm1, hl1, ht1⟩, hall⟩ := hw
  rw [hmh] at hmh0
  have e0 : mh = mh0 := Option.some.inj hmh0
  subst e0
  have e : mh.loc = ⟨l, mh.loc.offset⟩ := by
    rw [← hlab]
  refine ⟨a0, a1, usS, hus, hblk, ⟨mh.loc.offset, x.1, f1, m1, ?_, hf0, hf1, hm1, ?_, ht1⟩, hall⟩
  · rw [← e]; exact hlo
  · rw [hl1]; exact e

#print axioms witB_of_witH

/-- (WA, item kept) **The holder witness is kept** along a step that keeps memory's prefix and
adds promises only above the old memory, while the item is kept. -/
theorem witH_keep {E E' : TEnv} {s s' : St} {l : AllocLabel}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hnew : ∀ t, t ∈ s'.promises → t ∉ s.promises → s.mem.size ≤ t)
    (hPA : ∀ a t, t < s.mem.size → t ∈ PromAt E' s' a → t ∈ PromAt E s a)
    (hw : WitH E s l x) : WitH E' s' l x := by
  obtain ⟨a0, a1, usS, mh, hus, hmh, ha1, hblk, ⟨f1, m1, hf0, hf1, hm1, hl1, ht1⟩, hall⟩ := hw
  have hsz : ∀ {t m}, s.mem[t]? = some m → t < s.mem.size := fun h => lt_size_of_some h
  have hle : s.mem.size ≤ s'.mem.size := by
    rcases Nat.eq_zero_or_pos s.mem.size with h0 | h0
    · rw [h0]; exact Nat.zero_le _
    · have h1 := hpre (s.mem.size - 1) (by omega)
      rw [Array.getElem?_eq_getElem (by omega : s.mem.size - 1 < s.mem.size)] at h1
      have h2 : s.mem.size - 1 < s'.mem.size := lt_size_of_some (s := s') h1
      omega
  refine ⟨a0, a1, usS, mh, hus, by rw [hpre _ (hsz hmh)]; exact hmh, Nat.le_trans ha1 hle,
    fun t h0 h1 hp => ?_, ⟨f1, m1, hf0, hf1, by rw [hpre _ (hsz hm1)]; exact hm1, hl1, ht1⟩,
    fun o ho1 ho2 => ?_⟩
  · by_cases hin : t ∈ s.promises
    · exact hblk t h0 h1 hin
    · have h3 := hnew t hp hin
      omega
  · obtain ⟨f2, m2, hg0, hg1, hm2, hloc, hnp⟩ := hall o ho1 ho2
    exact ⟨f2, m2, hg0, hg1, by rw [hpre _ (hsz hm2)]; exact hm2, hloc,
      fun hp => hnp (hPA _ _ (hsz hm2) hp)⟩

#print axioms witH_keep

/-! ## (β′) merging a second item at the same holder (`TermTear.VRR_mix`) -/

/-- Master of `crItem_merge`, exposing the merged item's resources. -/
theorem crItem_mergeR {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {x y : Ts × Nat × Ty × List Word × Res × (Nat → Bool)}
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (hx : TermOverCr.CrItemQ E s cr l c x) (hy : TermOverCr.CrItemQ E s cr l c y) (hxy : y.1 = x.1)
    (hsum : x.2.2.2.2.1 + y.2.2.2.2.1 ≤ cr x.1) :
    y.2.1 = x.2.1 ∧ y.2.2.1 = x.2.2.1 ∧ ∃ x', x'.1 = x.1 ∧ x'.2.1 = x.2.1 ∧ x'.2.2.1 = x.2.2.1 ∧
      (∀ i, x'.2.2.2.2.2 i = (x.2.2.2.2.2 i || y.2.2.2.2.2 i)) ∧
      x'.2.2.2.2.1 ≤ x.2.2.2.2.1 + y.2.2.2.2.1 ∧ TermOverCr.CrItemQ E s cr l c x' := by
  obtain ⟨mh, usS, hmh, hlab, hlo, hnw, hat, hsol, husS, hq1, hq2, hwl, hvr, hR, hpin⟩ := hx
  obtain ⟨mh2, usS2, hmh2, -, -, -, hat2, hsol2, husS2, hq12, hq22, hwl2, hvr2, -, hpin2⟩ := hy
  rw [hxy, hmh] at hmh2
  have e0 : mh = mh2 := Option.some.inj hmh2
  subst e0
  have hP : TermPiece.Piece c.ty x.2.1 x.2.2.1 := ⟨hat, hsol, fun h => by
    rw [wc_of_accs husS] at h
    have h0 : nWords usS = 0 := Option.some.inj h
    have h1 : mh.loc.offset < x.2.1 + nWords usS := hq2
    rw [h0, Nat.add_zero] at h1
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 hq1)⟩
  have hP2 : TermPiece.Piece c.ty y.2.1 y.2.2.1 := ⟨hat2, hsol2, fun h => by
    rw [wc_of_accs husS2] at h
    have h0 : nWords usS2 = 0 := Option.some.inj h
    have h1 : mh.loc.offset < y.2.1 + nWords usS2 := hq22
    rw [h0, Nat.add_zero] at h1
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 hq12)⟩
  obtain ⟨eb, eS⟩ := TermPlant.piece_match hP hP2 (wc_of_accs husS) (wc_of_accs husS2) hq1 hq2 hq12 hq22
  rw [← eS] at husS2
  rw [husS] at husS2
  cases husS2
  have hcS := TermStep.coupledOK_AtOff hat hcpl
  have hiS := TermPlant.iallOK_ofNIP _ [] (TermIall.noIallV_AtOff hat hni)
  have hv2 : ValOfR E x.2.2.1 y.2.2.2.1 y.2.2.2.2.1 := by rw [eS]; exact hvr2
  obtain ⟨Rm, hvm, hRm⟩ := TermTear.VRR_mix (sel := x.2.2.2.2.2) hcS hiS husS hvr.1 hv2.1 hwl hwl2
  refine ⟨eb.symm, eS.symm, (x.1, x.2.1, x.2.2.1, TermTear.mixU usS x.2.2.2.2.2 x.2.2.2.1 y.2.2.2.1, Rm,
    fun i => x.2.2.2.2.2 i || y.2.2.2.2.2 i), rfl, rfl, rfl, fun _ => rfl, hRm, mh, usS, hmh, hlab, hlo, hnw, hat,
    hsol, husS, hq1, hq2, TermTear.length_mixU _ _ _ _ hwl hwl2,
    ⟨hvm, TermTear.Valid_mix husS hvr.2 hv2.2 hwl hwl2⟩, fun k => ?_, fun i o w tw' hK hI hw hL => ?_⟩
  · have a1 := hRm k; have a2 := hsum k
    simp only [Res.add_apply] at a1 a2 ⊢; omega
  · change (x.2.2.2.2.2 i || y.2.2.2.2.2 i) = true at hK
    change (TermTear.mixU usS x.2.2.2.2.2 x.2.2.2.1 y.2.2.2.1)[o]? = some w at hw
    rw [TermTear.mixU_getElem usS x.2.2.2.2.2 _ _ i o hwl hwl2 hI] at hw
    by_cases hk1 : x.2.2.2.2.2 i = true
    · simp only [hk1, ↓reduceIte] at hw
      exact hpin i o w tw' hk1 hI hw hL
    · simp only [hk1, Bool.false_eq_true, ↓reduceIte, Bool.false_or] at hw hK
      have hL2 : TermPlant.LowOwn s ⟨l, y.2.1 + o⟩ tw' := by rw [← eb]; exact hL
      have := hpin2 i o w tw' hK hI hw hL2
      rw [← eb] at this
      exact this

/-- **Two credited items at one holder merge into one** (per access unit: `x`'s words at `x`'s
units, `y`'s elsewhere), pinned at both items' units, carrying at most both items'
resources.  The cell type is `coupledOK` (`MemInv_cplT`) and `∀`-free (`StoNI`); the piece
inherits both (`coupledOK_AtOff`, `noIallV_AtOff`). -/
theorem crItem_merge {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {x y : Ts × Nat × Ty × List Word × Res × (Nat → Bool)}
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (hx : TermOverCr.CrItemQ E s cr l c x) (hy : TermOverCr.CrItemQ E s cr l c y) (hxy : y.1 = x.1)
    (hsum : x.2.2.2.2.1 + y.2.2.2.2.1 ≤ cr x.1) :
    y.2.1 = x.2.1 ∧ y.2.2.1 = x.2.2.1 ∧ ∃ x', x'.1 = x.1 ∧ x'.2.1 = x.2.1 ∧ x'.2.2.1 = x.2.2.1 ∧
      (∀ i, x'.2.2.2.2.2 i = (x.2.2.2.2.2 i || y.2.2.2.2.2 i)) ∧ TermOverCr.CrItemQ E s cr l c x'
 := by
  obtain ⟨a, b, x', c1, c2, c3, c4, -, c5⟩ := crItem_mergeR hcpl hni hx hy hxy hsum
  exact ⟨a, b, x', c1, c2, c3, c4, c5⟩

#print axioms crItem_merge

/-- (β′, gd_fund) **The cover at a foreign store, old items upgraded in place**: `Gs'` has the
old holders (`hmap`), its items are credited at `cr + δ` and cover whatever the old items
covered (`hup`; e.g. an old item merged with the store's new drop item at its holder,
`crItem_merge`); the new items `Gn` have holders distinct from the upgraded items'; every unit
overtaken after the step was overtaken before, or is covered by an upgraded or a new item;
and a nonzero `δ` lands on a holder. -/
theorem overCr_interfM {E E' : TEnv} {s s' : St} {cr δ : Ts → Res} {l : AllocLabel} {c : Cell}
    {G G' : Nat → Ts → Prop}
    {Gs Gs' Gn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hI : ∀ o, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o) (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩)
    (hG : ∀ o tw, G' o tw → G o tw)
    (h : TermOverCr.OverCrL E s cr l c G Gs)
    (hmap : Gs'.map (·.1) = Gs.map (·.1))
    (hitU : ∀ x ∈ Gs', TermOverCr.CrItemQ E s (fun t => cr t + δ t) l c x)
    (hwaU : ∀ x ∈ Gs', ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hup : ∀ o, (∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
      x.2.2.2.2.2 i = true) → ∃ x ∈ Gs', ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧
        InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true)
    (hGn : ∀ x ∈ Gn, TermOverCr.CrItemQ E s (fun t => cr t + δ t) l c x)
    (hnd : (Gn.map (·.1)).Nodup)
    (hdisj : ∀ x ∈ Gs', ∀ y ∈ Gn, x.1 ≠ y.1)
    (hwaN : ∀ x ∈ Gn, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hcovN : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw → G' o tw →
      TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw ∨
      ∃ x ∈ Gs' ++ Gn, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true)
    (hδ : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → δ t ≠ .zero →
      t ∈ (Gs' ++ Gn).map (·.1)) :
    TermOverCr.OverCrL E' s' (fun t => cr t + δ t) l c G' (Gs' ++ Gn) := by
  have hpr1 : ∀ t, t ∈ s.promises → t ∈ s'.promises := fun t ht => by rw [hpr]; exact ht
  have hnew : ∀ t, t ∈ s'.promises → t ∉ s.promises → s.mem.size ≤ t := fun t ht hn => by
    rw [hpr] at ht; exact absurd ht hn
  have hcr2 : ∀ t, t ∈ s.promises → cr t + δ t ≤ cr t + δ t := fun t _ => Res.le_refl _
  obtain ⟨hnd0, -, hcov, -, hz⟩ := h
  have hlow' : ∀ a tw, TermPlant.LowOwn s' a tw → TermPlant.LowOwn s a tw := fun a tw hl =>
    TermOverCr.lowOwn_back hpre hpr1 hP hl (by rw [← hpr]; exact hl.1)
  refine ⟨?_, fun x hx => ?_, fun o tw hi hv hl hg hov => ?_, fun x hx usS i o h1 h2 h3 => ?_,
    fun t m ht hm hl hw hnz => ?_⟩
  · rw [List.map_append, hmap]
    refine List.nodup_append.2 ⟨hnd0, hnd, fun a ha b hb => ?_⟩
    rw [← hmap] at ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact hdisj x hx y hy
  · rcases List.mem_append.1 hx with hx | hx
    · exact TermOverCr.crItem_frame hpre hpr1 hnew hP hsto hV hcr2 (hwaU x hx) hPU (hitU x hx)
    · exact TermOverCr.crItem_frame hpre hpr1 hnew hP hsto hV hcr2 (hwaN x hx) hPU (hGn x hx)
  · have hl0 := hlow' _ _ hl
    rcases hcovN o tw hi hv hl0 hg hov with hold | hr
    · obtain ⟨x, hx, hr⟩ := hup o (hcov o tw (hI o hi) (hVU o hv) hl0 (hG o tw hg) hold)
      exact ⟨x, List.mem_append_left _ hx, hr⟩
    · exact hr
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨t0, h0⟩ := hwaU x hx usS i o h1 h2 h3
      exact ⟨t0, TermOverCr.lowOwn_fwd hpre hpr1 hnew hP h0⟩
    · obtain ⟨t0, h0⟩ := hwaN x hx usS i o h1 h2 h3
      exact ⟨t0, TermOverCr.lowOwn_fwd hpre hpr1 hnew hP h0⟩
  · have ht0 : t ∈ s.promises := by rw [← hpr]; exact ht
    have hm0 : s.mem[t]? = some m := by rw [← hpre t (hP t ht0)]; exact hm
    have hw0 : ¬ WordUnit E m.loc := fun hw0 => hw (by
      obtain ⟨c1, hc1, hor⟩ := hw0
      exact ⟨c1, by rw [hl, hsto, ← hl]; exact hc1, hor⟩)
    by_cases hd : δ t = .zero
    · have hnz0 : cr t ≠ .zero := fun h0 => hnz (by
        show cr t + δ t = .zero
        rw [h0, hd]; rfl)
      rw [List.map_append, hmap]
      exact List.mem_append_left _ (hz t m ht0 hm0 hl hw0 hnz0)
    · exact hδ t m ht0 hm0 hl hd

#print axioms overCr_interfM

/-- (β′) **An in-place upgrade's bookkeeping**: mapping each old item to one at the same
holder, piece and type, with at least its units, keeps the holders (`hmap`), the cover (`hup`)
and the holder-unit clause. -/
theorem upgrade_of {Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (f : (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) → (Ts × Nat × Ty × List Word × Res × (Nat → Bool)))
    (hf : ∀ x ∈ Gs, (f x).1 = x.1 ∧ (f x).2.1 = x.2.1 ∧ (f x).2.2.1 = x.2.2.1 ∧
      ∀ i, x.2.2.2.2.2 i = true → (f x).2.2.2.2.2 i = true) :
    (Gs.map f).map (·.1) = Gs.map (·.1) ∧
    (∀ o, (∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
      x.2.2.2.2.2 i = true) → ∃ x ∈ Gs.map f, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧
        InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true) := by
  refine ⟨?_, fun o ⟨x, hx, usS, i, h1, h2, h3, h4⟩ => ?_⟩
  · rw [List.map_map]
    exact List.map_congr_left (fun x hx => (hf x hx).1)
  · obtain ⟨e1, e2, e3, hK⟩ := hf x hx
    exact ⟨f x, List.mem_map.2 ⟨x, hx, rfl⟩, usS, i, by rw [e3]; exact h1, by rw [e2]; exact h2,
      by rw [e2]; exact h3, hK i h4⟩

#print axioms upgrade_of

/-- (β′, `Pδ` target) **A plant credit at a promise in an item's piece sits at the item's
holder**: `HolderLow` puts the holder at or below it, and the credit's window lowness puts it at
or below the holder. -/
theorem target_eq_holder {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} {usS : List Acc} {m : Msg} {t : Ts} {R : Res}
    (hsto : E.sto l = some c) (hx : TermOverCr.CrItemQ E s cr l c x) (hHL : TermOverCr.HolderLow s l [x])
    (hus : accs x.2.2.1 = some usS) (ht : t ∈ s.promises) (hm : s.mem[t]? = some m)
    (hlab : m.loc.label = l) (h1 : x.2.1 ≤ m.loc.offset) (h2 : m.loc.offset < x.2.1 + nWords usS)
    (hP : PlantCr E s m t R) : t = x.1 := by
  have hle1 : x.1 ≤ t := hHL x (List.mem_singleton_self x) usS hus t m ht hm hlab h1 h2
  obtain ⟨c', sb, S0, b0, S, us, wb, hsto', -, -, hseg, hat, hS, -, hus', hn, hlo, hhi, htw, -, -, hlow, -⟩ := hP
  rw [hlab, hsto] at hsto'
  cases hsto'
  obtain ⟨mh, usS2, hmh, hlabh, hloh, -, hatx, hsolx, husx, hq1, hq2, -⟩ := hx
  rw [hus] at husx
  cases husx
  have hPc := TermPlant.plant_piece hseg hat hS (wc_of_accs hus') hn
  have hPx : TermPiece.Piece c.ty x.2.1 x.2.2.1 := ⟨hatx, hsolx, fun h => by
    rw [wc_of_accs hus] at h
    have h0 : nWords usS = 0 := Option.some.inj h
    rw [h0, Nat.add_zero] at h2
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 h1)⟩
  obtain ⟨eb, eS⟩ := TermPlant.piece_match hPc hPx (wc_of_accs hus') (wc_of_accs hus) hlo hhi h1 h2
  rw [eS] at hus'
  rw [hus] at hus'
  cases hus'
  have hle2 : t ≤ x.1 := hlow x.1 mh hloh.1 hmh (by rw [hlabh, hlab]) (by rw [eb]; exact hq1)
    (by rw [eb]; exact hq2) (Nat.le_trans hle1 htw)
  exact Nat.le_antisymm hle2 hle1

#print axioms target_eq_holder

end TermOverCrW

