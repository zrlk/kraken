import WeakCore.TermPoolBal

/-! **The sharp pool split at a thread step**.  The stepper's kept pool
(`plStep`, zero at discharged promises) plus its pool at the promises the step discharges (`plDis`)
is at most its old pool sum plus the step's new items: the discharged pool is released, not lost
slack (`TermPoolBal.plStep_le` drops it).  For form P of the `IneqH` pool term. -/

namespace TermPoolSplit
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCrBII TermBal TermOwnFresh TermPoolStaging TermPoolBal
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The stepping thread's pool at the promises its step discharges (absent after the step). -/
noncomputable def plDis (pl : Nat → Ts → Res) (i : Nat) (s' : St) : Ts → Res := by
  classical
  exact fun t => if t ∈ s'.promises then .zero else pl i t

/-- A nodup sublist's sum plus the sum off it is at most the whole sum. -/
theorem nsum_split {f : Ts → Nat} {L L' : List Ts} [DecidablePred (· ∈ L')] (hnd : L'.Nodup)
    (hsub : ∀ x ∈ L', x ∈ L) :
    (L'.map f).sum + (L.map (fun t => if t ∈ L' then 0 else f t)).sum ≤ (L.map f).sum := by
  have h1 : (L'.map f).sum = (L'.map (fun t => if t ∈ L' then f t else 0)).sum := by
    congr 1
    exact List.map_congr_left fun t ht => by simp only [ht, ↓reduceIte]
  have h2 : (L'.map (fun t => if t ∈ L' then f t else 0)).sum ≤ (L.map (fun t => if t ∈ L' then f t else 0)).sum :=
    nsum_le_of_nodup L hnd (fun x hx _ => hsub x hx)
  have h3 : (L.map f).sum = (L.map (fun t => if t ∈ L' then f t else 0)).sum +
      (L.map (fun t => if t ∈ L' then 0 else f t)).sum := by
    rw [← tsum_map_add]
    congr 1
    exact List.map_congr_left fun t _ => by by_cases h : t ∈ L' <;> simp only [h, ↓reduceIte, Nat.add_zero, Nat.zero_add]
  omega

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **The sharp split** (sharpens `TermPoolBal.plStep_le` by the discharged pool). -/
theorem plStep_split (hN : PromNodupR p k arch Sp c0) {c cq : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c cq Eg Tot HP HS cr db i th r) (pl : Nat → Ts → Res) (plh : Ts → Res)
    (key : Key) :
    pSum (stOf r.1 r.2.1 r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) key +
        pSum (stOf c.mem c.pairs th) (plDis pl i (stOf r.1 r.2.1 r.2.2)) key ≤
      pSumAt c i (pl i) key + pSum (stOf r.1 r.2.1 r.2.2) plh key := by
  classical
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
  have hsub := (TermFul.tstep_fulfil (fun t ht => X.inv.plt i th t X.hth ht) (MemInv_nopair hm0) X.hr).1
  have hnd : r.2.2.promises.Nodup := hsub.nodup (hN c X.run i th X.hth)
  rw [pSumAt_some X.hth, pSum_key, pSum_key, pSum_key, pSum_key]
  have e : ∀ t ∈ (stOf r.1 r.2.1 r.2.2).promises,
      plStep pl i (stOf r.1 r.2.1 r.2.2) plh t key = pl i t key + plh t key := fun t ht => by
    simp only [plStep, ht, ↓reduceIte, Res.add_apply]
  have e2 : ∀ t ∈ (stOf c.mem c.pairs th).promises,
      plDis pl i (stOf r.1 r.2.1 r.2.2) t key = if t ∈ r.2.2.promises then 0 else pl i t key := fun t _ => by
    by_cases h : t ∈ r.2.2.promises
    · have h' : t ∈ (stOf r.1 r.2.1 r.2.2).promises := h
      simp only [plDis, h', h, ↓reduceIte, Res.zero_apply]
    · have h' : t ∉ (stOf r.1 r.2.1 r.2.2).promises := h
      simp only [plDis, h', h, ↓reduceIte]
  rw [List.map_congr_left e, List.map_congr_left e2, tsum_map_add (fun t => pl i t key) (fun t => plh t key)]
  have hs := nsum_split (f := fun t => pl i t key) (L := th.promises) hnd (fun x hx => hsub.subset hx)
  have ep : (stOf c.mem c.pairs th).promises = th.promises := rfl
  have ep' : (stOf r.1 r.2.1 r.2.2).promises = r.2.2.promises := rfl
  rw [ep, ep']
  omega

end

end TermPoolSplit

#print axioms TermPoolSplit.nsum_split
#print axioms TermPoolSplit.plStep_split
