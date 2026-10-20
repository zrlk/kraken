import WeakCore.TermOverCrF

/-! # TermOverCrD: the new items of a foreign store (Dn builder)

Each drop entry `g` of the store's list at the owner's cell `l` with a target promise `t`
(`tg g = some t`) gives the item `(t, g.b, g.S, g.ws, g.R, kfOf … g)`.  The mask `kfOf`
selects the access units at which every word has a lowest own promise meeting the
`gd_itemW` side conditions, so items are credited and window-safe by construction.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The side condition at word `o` of entry `g`, for `gd_itemW`. -/
def KOk (E : TEnv) (s : St) (l : AllocLabel) (g : TermPiece.GdE) (o : Nat) : Prop :=
  (∃ t0, TermPlant.LowOwn s ⟨l, g.b + o⟩ t0) ∧
    ∀ tw', TermPlant.LowOwn s ⟨l, g.b + o⟩ tw' →
      g.L o = true ∧ (tw' ∈ PromAt E s ⟨l, g.b + o⟩ ∨ (PredU E ⟨l, g.b + o⟩ ∧ FirstW s.mem ⟨l, g.b + o⟩ tw')) ∧
      (∀ t m, tw' < t → s.mem[t]? = some m → m.loc = ⟨l, g.b + o⟩ → t ∈ PromAt E s ⟨l, g.b + o⟩) ∧
      TermOverCr.WinG E s l (g.b + o) tw'

/-- The unit mask of entry `g`: units all of whose words meet `KOk`. -/
noncomputable def kfOf (E : TEnv) (s : St) (l : AllocLabel) (g : TermPiece.GdE) (i : Nat) : Bool := by
  classical
  exact decide (∃ us, accs g.S = some us ∧ ∀ o, InAcc us i o → KOk E s l g o)

theorem kfOf_spec {E : TEnv} {s : St} {l : AllocLabel} {g : TermPiece.GdE} {i : Nat} {us : List Acc}
    (hus : accs g.S = some us) (h : kfOf E s l g i = true) : ∀ o, InAcc us i o → KOk E s l g o := by
  classical
  unfold kfOf at h
  obtain ⟨us', hus', hk⟩ := of_decide_eq_true h
  rw [hus] at hus'
  cases hus'
  exact hk

/-- **The new items of a foreign store are credited** at `cr + δ` and window-safe. -/
theorem dn_items {Eg : GEnv} {c : Cfg} {j k : Nat} {thj thk : TTh} {Sj Sk : AllocLabel → Prop}
    {cr δ : Ts → Res} {l : AllocLabel} {cl : Cell} {tg : TermPiece.GdE → Option Ts}
    {Gd : List TermPiece.GdE}
    (hP : PromsOK Eg c) (hj : c.ths[j]? = some thj) (hk : c.ths[k]? = some thk) (hsh : Eg.Shared l)
    (hpf : Eg.pfr l ≠ none) (hc : (Cut Eg j Sj).sto l = some cl)
    (hGd : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t →
      TermPiece.GdOK (Cut Eg k Sk) (stOf c.mem c.pairs thk) g ∧ noOR g.S = true ∧
      ∃ us mh, accs g.S = some us ∧ c.mem[t]? = some mh ∧ mh.loc.label = l ∧
        TermPlant.LowOwn (stOf c.mem c.pairs thj) mh.loc t ∧ ¬ WordUnit (Cut Eg j Sj) mh.loc ∧
        g.b ≤ mh.loc.offset ∧ mh.loc.offset < g.b + nWords us)
    (hR : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, y.2.2.2.2.1 ≤ δ y.1) :
    (∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj) (fun t => cr t + δ t) l cl y) ∧
    (∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0) := by
  refine ⟨fun y hy => ?_, fun y hy usS i o h1 h2 h3 => ?_⟩
  · have hRy := hR y hy
    obtain ⟨g, hg, hgl, t, ht, rfl⟩ := mem_dnOf.1 hy
    obtain ⟨hok, hnr, us, mh, hus, hm, hlab, hlow, hnw, h1, h2⟩ := hGd g hg hgl t ht
    refine gd_itemWQ hP hj hk hsh hpf hc hgl hok hnr hus hm hlab hlow hnw h1 h2
      (Res.le_trans hRy (fun _ => by simp)) (fun i o tw' hKi hio hl => ?_)
    exact (kfOf_spec hus hKi o hio).2 tw' hl
  · obtain ⟨g, -, -, t, -, rfl⟩ := mem_dnOf.1 hy
    exact (kfOf_spec h1 h2 o h3).1

end TermOverCrW

#print axioms TermOverCrW.kfOf_spec
#print axioms TermOverCrW.dn_items
