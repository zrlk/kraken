import WeakCore.TermPredHold
import WeakCore.TermMainDefs
import WeakCore.TermPlantF

/-!
# TermPredHoldP (draft): `PredHoldG` preservation and its consumer

* `OwnPredStoreFree`: the run fact the owner's thread step needs (PlantView, B2/D2).
* `predHold_prom`: a promise step (old holders persist; a plant's new predicted units are held by
  `PrefixHeld`, and by `PrivCoh` the first write there is an own promise).
-/

namespace TermPredHoldP

open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermMem TermStep TermCut TermMain
  TermPredHold
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (PredHold, owner thread step) **The owner never fulfils a predicted holder** except by making
the unit real: at a thread step of `i` (`TCtx`) with post-environment `E'` (`EFoot` from the cut
`Cut Eg i S`), if `a` is a predicted unit of `i`'s unpublished own cell and its first write `h` is
an outstanding promise of `i` that the step fulfils, then `a` is below the real count at `E'`. -/
def OwnPredStoreFree (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop)
    (c0 : Cfg) : Prop :=
  ∀ (c c' : Cfg) (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) (i : Nat)
    (th : TTh) (r : Memory × List Ts × TTh) (S : AllocLabel → Prop) (E' : TEnv),
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
    EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) →
    ∀ (a : Address) (cl : Cell) (h : Ts), Eg.sto a.label = some cl → cl.owner = some i →
      ¬ Eg.pubd a.label → PredU (Cut Eg i S) a → FirstW c.mem a h → h ∈ th.promises →
      h ∉ r.2.2.promises → IniWr E' a

/-- (plant side) **The planted counts are held**: at every planted label the count `N l` is
within the buffer and its prefix is held by the promiser (`PrefixHeld_NpZ`, `NpZ_le` for
`TermPlantF.plantOf`/`plantN`). -/
def PlantHeld (Eg : GEnv) (c : Cfg) (th : TTh) (j : Nat) (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) :
    Prop :=
  ∀ l f cl Na e, P l = some f → Eg.sto l = some cl → cl.ty = .array (.lit Na) e →
    PrefixHeld (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l cl (N l) ∧ N l ≤ Na ∧
      ∀ u, HoldW (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l u → u ≤ f

/-- **`PredHoldG` after a promise step** of `j` with plant `P`, counts `N`. -/
theorem predHold_prom {Eg : GEnv} {c : Cfg} {g : G} {j : Nat} {th : TTh} {S0 : AllocLabel → Prop}
    {a0 : Address} {v : WeakMem.Val} {w : Ts} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {n n' : Nat}
    (hH : PredHoldG Eg c) (hth : c.ths[j]? = some th)
    (hm : MemInv g (Cut Eg j S0) (stOf c.mem c.pairs th)) (hNU : PromNotUndef c)
    (hsp : PlantSpec Eg P j n) (hheld : PlantHeld Eg c th j P N) :
    PredHoldG (EgP Eg P N j n') (promise c j a0 v w) := by
  intro q thq S a hq ⟨cl, hcl, hown⟩ hpd hpu
  have hpi := promise_inv (a := a0) (v := v) (w := w) hth
  have hmem : (promise c j a0 v w).mem = c.mem.push ⟨a0, v, w⟩ := by rw [hpi.1]
  have hcl0 : Eg.sto a.label = some cl := hcl
  have hpd0 : ¬ Eg.pubd a.label := hpd
  -- the promiser's promises only grow; other threads unchanged
  have hgrow : ∀ thq0, c.ths[q]? = some thq0 → ∀ t, t ∈ thq0.promises → t ∈ thq.promises := by
    intro thq0 hq0 t ht
    by_cases hqj : q = j
    · subst hqj
      rw [hth] at hq0; cases hq0
      rw [hpi.2.1] at hq; cases hq
      exact List.mem_append_left _ ht
    · rw [TermStep.promise_other hqj] at hq; rw [hq] at hq0; cases hq0; exact ht
  obtain ⟨thq0, hq0⟩ : ∃ thq0, c.ths[q]? = some thq0 := by
    by_cases hqj : q = j
    · subst hqj; exact ⟨th, hth⟩
    · rw [TermStep.promise_other hqj] at hq; exact ⟨thq, hq⟩
  obtain ⟨hpf', hi', N1, e1, us1, hT1, hu1, hge'⟩ := predU_own (Eg := EgP Eg P N j n') hcl hown hpu
  cases hP : P a.label with
  | none =>
    -- not planted here: the unit was predicted before
    have hpf0 : Eg.pfr a.label ≠ none := by
      have e : (EgP Eg P N j n').pfr a.label = Eg.pfr a.label := by
        show (plantG Eg P N).pfr a.label = _; simp only [plantG, hP]
      rw [e] at hpf'; exact hpf'
    have hini0 : (EgP Eg P N j n').ini a.label = Eg.ini a.label := by
      show (plantG Eg P N).ini a.label = _; simp only [plantG, hP]
    have hpu0 : PredU (Cut Eg q S) a :=
      predU_of hcl0 hown hpf0 (fun N e us hT hu => by rw [← hini0]; exact hi' N e us hT hu)
        ⟨N1, e1, us1, hT1, hu1, by rw [← hini0]; exact hge'⟩
    obtain ⟨h, hf, hh, hhF⟩ := hH q thq0 S a hq0 ⟨cl, hcl0, hown⟩ hpd0 hpu0
    have hpe : (EgP Eg P N j n').pfr a.label = Eg.pfr a.label := by
      show (plantG Eg P N).pfr a.label = _; simp only [plantG, hP]
    exact ⟨h, by rw [hmem]; exact FirstW_push _ hf, hgrow thq0 hq0 h hh, fun F hF => hhF F (by rw [← hpe]; exact hF)⟩
  | some f =>
    -- planted here: a cell of the promiser without a frontier before
    obtain ⟨hpn, ⟨cl2, hcl2, hown2⟩, -, -⟩ := hsp a.label f hP
    rw [hcl0] at hcl2; cases hcl2
    have hqj : q = j := by rw [hown] at hown2; cases hown2; rfl
    subst hqj
    rw [hth] at hq0; cases hq0
    have hini1 : (EgP Eg P N q n').ini a.label = max (Eg.ini a.label) (N a.label) := by
      show (plantG Eg P N).ini a.label = _; simp only [plantG, hP]
    have hri1 : (EgP Eg P N q n').rini a.label = Eg.rini a.label := rfl
    -- private before: `ini ≤ rc` (OwnHidP), so the unit lies at or above `ini`
    have hcC : (Cut Eg q S0).sto a.label = some cl := cutSto_own hcl0 hown
    have hle0 : Eg.ini a.label ≤ Eg.rini a.label := by
      refine Nat.le_of_not_lt fun hlt => ?_
      obtain ⟨f0, hf0, -⟩ := hm.2.2.2.2.2.1.2 a.label cl hcC hown
        (show min (Eg.ini a.label) (Eg.rini a.label) < Eg.ini a.label by
          rw [Nat.min_eq_right (Nat.le_of_lt hlt)]; exact hlt)
      have : Eg.pfr a.label = some f0 := hf0
      rw [hpn] at this; cases this
    rw [hini1, hri1] at hge'
    have hgeI : Eg.ini a.label * nWords us1 ≤ a.offset := by
      have : Eg.ini a.label ≤ min (max (Eg.ini a.label) (N a.label)) (Eg.rini a.label) :=
        Nat.le_min.2 ⟨Nat.le_max_left _ _, hle0⟩
      exact Nat.le_trans (Nat.mul_le_mul_right _ this) hge'
    have hlt1 := hi' N1 e1 us1 hT1 hu1
    rw [hini1] at hlt1
    obtain ⟨hPH, hNa, hHf⟩ := hheld a.label f cl N1 e1 hP hcl0 hT1
    have hltN : a.offset < N a.label * nWords us1 := by
      rcases Nat.le_total (Eg.ini a.label) (N a.label) with h | h
      · rw [Nat.max_eq_right h] at hlt1; exact hlt1
      · rw [Nat.max_eq_left h] at hlt1; exact absurd hlt1 (Nat.not_lt.2 hgeI)
    rcases hPH N1 e1 us1 hT1 hu1 a.offset hltN with hI | ⟨u, hu, mu, hmu, hloc⟩
    · have : a.offset < Eg.ini a.label * nWords us1 := hI N1 e1 us1 hT1 hu1
      exact absurd this (Nat.not_lt.2 hgeI)
    · have hu' : u ∈ th.promises := hu
      have hmu' : c.mem[u]? = some mu := hmu
      have hnu := hNU q th u mu hth hu' hmu'
      obtain ⟨h, hf, -⟩ := firstW_ex u mu hmu' (by rw [hloc]) hnu
      -- the first write is an own promise: off promises the private unit holds only `undef`
      have hh : h ∈ th.promises := by
        refine Classical.byContradiction fun hn => ?_
        obtain ⟨⟨mh, hmh, hlh, hvh⟩, -⟩ := hf
        have hPU : PrivU (Cut Eg q S0) mh.loc := by
          rw [hlh]
          refine ⟨cl, N1, e1, us1, hcC, hown, hpn, hT1, hu1, ?_, ?_⟩
          · show min (Eg.ini a.label) (Eg.rini a.label) * nWords us1 ≤ a.offset
            rw [Nat.min_eq_left hle0]; exact hgeI
          · exact Nat.lt_of_lt_of_le hltN (Nat.mul_le_mul_right _ hNa)
        exact hvh (hm.2.2.2.1.2 h mh hn hmh hPU).2
      -- (G1) the holder is a `HoldW` witness of the plant, hence at most the planted frontier
      have hhf : h ≤ f := by
        obtain ⟨mh, hmh, hlh, -⟩ := hf.1
        refine hHf h ⟨h, hh, mh, hmh, by rw [hlh], Nat.le_refl _, fun u hu m' hm' hl' => ?_, ?_⟩
        · rw [hlh] at hl'
          exact holder_min hf hm' hl' (hNU q th u m' hth hu hm')
        · intro hw
          have hcP : (TermPlantF.cutP Eg q).sto a.label = some cl := cutSto_own hcl0 hown
          rw [hlh] at hw
          have := hw cl N1 e1 us1 hcP hT1 hu1
          exact absurd (Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ (Nat.min_le_left _ _))) (Nat.not_lt.2 hgeI)
      have hpe : (EgP Eg P N q n').pfr a.label = some f := by
        show (plantG Eg P N).pfr a.label = _; simp only [plantG, hP]
      exact ⟨h, by rw [hmem]; exact FirstW_push _ hf, hgrow th hth h hh,
        fun F hF => by rw [hpe] at hF; cases hF; exact hhf⟩


/-- **`PredHoldG` after a thread step** of `i` with footprint `E'` (`EFoot` from the cut, plus the
ini-refinement `hIL`: an own count rises only up to the real count), memory extended, other
threads unchanged, and the owner's fulfilments of predicted holders excluded (`hops`, from
`OwnPredStoreFree`). -/
theorem predHold_thread {Eg : GEnv} {c c' : Cfg} {g : G} {i : Nat} {th th' : TTh} {S : AllocLabel → Prop}
    {E' : TEnv} {s s' : St} {F : Nat → List Ts}
    (hH : PredHoldG Eg c) (hth : c.ths[i]? = some th) (hi' : c'.ths[i]? = some th')
    (hoth : ∀ j, j ≠ i → c'.ths[j]? = c.ths[j]?)
    (hext : ∀ t, t < c.mem.size → c'.mem[t]? = c.mem[t]?)
    (hF : EFoot g (Cut Eg i S) E' s s') (hfr : GFreshE g Eg s.nalloc s'.nalloc)
    (hIL : ∀ l, OwnAt (Cut Eg i S) l → E'.ini l ≤ max (Eg.ini l) (E'.rini l))
    (hm : MemInv g (Cut Eg i S) s)
    (hops : ∀ (a : Address) (cl : Cell) (h : Ts), Eg.sto a.label = some cl → cl.owner = some i →
      ¬ Eg.pubd a.label → PredU (Cut Eg i S) a → FirstW c.mem a h → h ∈ th.promises →
      h ∉ th'.promises → IniWr E' a) :
    PredHoldG ((Eg.post g s.nalloc s'.nalloc E').withFp F) c' := by
  intro q thq S' a hq ⟨cl, hcl, hown⟩ hpd hpu
  obtain ⟨-, -, hsto, -, hini, hpfr, -, -, -, hri, -, -, hrq, -⟩ := hF
  have hpd' : ¬ (Eg.pubd a.label ∨ (Eg.pfr a.label = none ∧ E'.pfr a.label ≠ none ∧ E'.seen a.label)) := hpd
  have hpd0 : ¬ Eg.pubd a.label := fun h => hpd' (Or.inl h)
  obtain ⟨hpf', hi1, N1, e1, us1, hT1, hu1, hge'⟩ := predU_own (S := S') hcl hown hpu
  change E'.pfr a.label ≠ none at hpf'
  change ∀ N e us, cl.ty = .array (.lit N) e → accs e = some us → a.offset < E'.ini a.label * nWords us at hi1
  change min (E'.ini a.label) (E'.rini a.label) * nWords us1 ≤ a.offset at hge'
  -- not a fresh label (a fresh cell has no frontier)
  have hnF : ¬ FreshIn g s.nalloc s'.nalloc a.label := by
    intro hFr
    obtain ⟨h0, -, hp0⟩ := hfr a.label hFr
    rcases hpfr a.label with e | ⟨-, -, -, -, -, ⟨c1, hc1, -⟩, -⟩ | ⟨-, -, hs0⟩
    · exact hpf' (by rw [e]; exact hp0)
    · rw [cutSto_sub hc1] at h0; cases h0
    · have : (Eg.post g s.nalloc s'.nalloc E').sto a.label = some cl := hcl
      rw [post_sto_fresh hFr, hs0] at this; cases this
  have hcl0 : Eg.sto a.label = some cl := by
    have : (Eg.post g s.nalloc s'.nalloc E').sto a.label = some cl := hcl
    rw [post_sto_old hnF] at this; exact this
  by_cases hqi : q = i
  · subst hqi
    have hsE : E'.sto a.label = some cl := by
      rcases hsto a.label with e | ⟨hFr, -⟩
      · rw [e]; exact cutSto_own hcl0 hown
      · exact absurd hFr hnF
    have hOA : OwnAt (Cut Eg q S) a.label := ⟨cl, cutSto_own hcl0 hown, hown⟩
    have hIL1 := hIL a.label hOA
    have hri1 : Eg.rini a.label ≤ E'.rini a.label := hri a.label
    have hini1 : Eg.ini a.label ≤ E'.ini a.label := (hini a.label).1
    -- the count stayed (else the unit would be real)
    have hlt : E'.rini a.label < E'.ini a.label := by
      refine Nat.lt_of_not_le fun hle => ?_
      have := hi1 N1 e1 us1 hT1 hu1
      rw [Nat.min_eq_left hle] at hge'
      exact absurd this (Nat.not_lt.2 hge')
    have hie : E'.ini a.label = Eg.ini a.label := by
      rcases Nat.le_total (Eg.ini a.label) (E'.rini a.label) with h | h
      · rw [Nat.max_eq_right h] at hIL1; omega
      · rw [Nat.max_eq_left h] at hIL1; omega
    -- the frontier was there before (else `ini ≤ rini` by OwnHidP)
    have hpf0 : Eg.pfr a.label ≠ none := by
      intro hn
      have hle0 : Eg.ini a.label ≤ Eg.rini a.label := by
        refine Nat.le_of_not_lt fun hlt0 => ?_
        obtain ⟨f0, hf0, -⟩ := hm.2.2.2.2.2.1.2 a.label cl (cutSto_own hcl0 hown) hown
          (show min (Eg.ini a.label) (Eg.rini a.label) < Eg.ini a.label by
            rw [Nat.min_eq_right (Nat.le_of_lt hlt0)]; exact hlt0)
        have : Eg.pfr a.label = some f0 := hf0
        rw [hn] at this; cases this
      omega
    have hpu0 : PredU (Cut Eg q S) a := by
      refine predU_of hcl0 hown hpf0 (fun N e us hT hu => by rw [← hie]; exact hi1 N e us hT hu)
        ⟨N1, e1, us1, hT1, hu1, Nat.le_trans (Nat.mul_le_mul_right _ ?_) hge'⟩
      rw [hie]; exact Nat.le_min.2 ⟨Nat.min_le_left _ _, Nat.le_trans (Nat.min_le_right _ _) hri1⟩
    obtain ⟨h, hf, hh, hhF⟩ := hH q th S a hth ⟨cl, hcl0, hown⟩ hpd0 hpu0
    rw [hi'] at hq; cases hq
    by_cases hk : h ∈ th'.promises
    · refine ⟨h, FirstW_grow hext hf, hk, fun F hF => hhF F ?_⟩
      have hF' : E'.pfr a.label = some F := hF
      rcases hpfr a.label with e | ⟨e, -⟩ | ⟨hFr, -⟩
      · rw [e] at hF'; exact hF'
      · exact absurd e hpf0
      · exact absurd hFr hnF
    · have hw := hops a cl h hcl0 hown hpd0 hpu0 hf hh hk
      have := hw cl N1 e1 us1 hsE hT1 hu1
      exact absurd this (Nat.not_lt.2 hge')
  · -- another thread's cell: untouched by the step
    have hnO : ¬ OwnAt (Cut Eg i S) a.label := fun ⟨c1, hc1, ho1⟩ => by
      rw [cutSto_sub hc1] at hcl0; cases hcl0
      rw [hown] at ho1; cases ho1; exact hqi rfl
    have hie : E'.ini a.label = Eg.ini a.label := by
      rcases (hini a.label).2 with e | e | e
      · exact e
      · exact absurd e hnF
      · exact absurd e.1 hnO
    have hre : E'.rini a.label = Eg.rini a.label := by
      rcases hrq a.label with e | e | e
      · exact e
      · exact absurd e hnF
      · exact absurd e hnO
    have hpe : E'.pfr a.label = Eg.pfr a.label := by
      rcases hpfr a.label with e | ⟨-, -, -, -, -, ho, -⟩ | ⟨e, -⟩
      · exact e
      · exact absurd ho hnO
      · exact absurd e hnF
    have hpu0 : PredU (Cut Eg q S) a :=
      predU_of hcl0 hown (by rw [← hpe]; exact hpf') (fun N e us hT hu => by rw [← hie]; exact hi1 N e us hT hu)
        ⟨N1, e1, us1, hT1, hu1, by rw [← hie, ← hre]; exact hge'⟩
    rw [hoth q hqi] at hq
    obtain ⟨h, hf, hh, hhF⟩ := hH q thq S a hq ⟨cl, hcl0, hown⟩ hpd0 hpu0
    exact ⟨h, FirstW_grow hext hf, hh, fun F hF => hhF F (by rw [← hpe]; exact hF)⟩


section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`PlantHeld` for the plant choice** `TermPlantF.plantOf`/`plantN` (`PrefixHeld_NpZ`, `NpZ_le`). -/
theorem plantHeld_of {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) :
    PlantHeld Eg c th j (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) := by
  intro l f cl Na e hpl hcl hT
  obtain ⟨hPL, -⟩ := TermPlantF.plantOf_some X.hth hpl
  have hcP : (TermPlantF.cutP Eg j).sto l = some cl := by
    obtain ⟨-, -, t1, -, m1, -, -, -, a1, g1, -, hal, cl1, hc1, -, -⟩ := hPL
    subst hal
    have e1 : cl1 = cl := by rw [cutSto_sub hc1] at hcl; cases hcl; rfl
    subst e1; exact hc1
  have hN : TermPlantF.plantN c Eg j a v w l = NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l := by
    simp only [TermPlantF.plantN, X.hth]
  rw [hN]
  refine ⟨PrefixHeld_NpZ hcP, NpZ_le hcP hT, fun u hu => ?_⟩
  obtain ⟨-, hf⟩ := TermPlantF.plantOf_some X.hth hpl
  rw [hf]; exact HoldW_le_plantF hu

/-- **`PredHoldG` after a promise step**, at a `PCtx`. -/
theorem predHold_promX {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (hH : PredHoldG Eg c)
    {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {n n' : Nat}
    (hsp : PlantSpec Eg P j n) (hheld : PlantHeld Eg c th j P N) :
    PredHoldG (EgP Eg P N j n') (promise c j a v w) := by
  obtain ⟨S0, -, -, hm, -⟩ := X.inv.thr j th X.hth
  exact predHold_prom hH X.hth hm X.inv.promNU hsp hheld

end

#print axioms predHold_prom
#print axioms plantHeld_of
#print axioms predHold_promX
#print axioms predHold_thread

/-- (IniLe) **The footprint's own-count bound**: at an own cell a thread step
raises the count only up to the real count. -/
theorem hIL_of_efoot {g : G} {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {E' : TEnv} {s s' : St}
    (hF : EFoot g (Cut Eg i S) E' s s') (hfr : GFreshE g Eg s.nalloc s'.nalloc) :
    ∀ l, OwnAt (Cut Eg i S) l → E'.ini l ≤ max (Eg.ini l) (E'.rini l) := by
  intro l hO
  rcases (hF.2.2.2.2.1 l).2 with e | hFr | ⟨-, hb, -⟩
  · rw [e]; exact Nat.le_max_left _ _
  · obtain ⟨c1, hc1, -⟩ := hO
    have h0 := (hfr l hFr).1
    rw [cutSto_sub hc1] at h0; cases h0
  · exact hb

#print axioms hIL_of_efoot

end TermPredHoldP
