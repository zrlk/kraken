import WeakCore.TermSpawnRun

/-!
# TermSpawnKidMem: the memory invariant of a kid spawned mid-run

A kid appended at index `n = c.ths.size` of a configuration whose other threads may hold promises.
Its cut owns nothing (`OwnLive`), so every own/seen clause of `MemInv` is vacuous and the kid's view
is never read.  The remaining clauses come from

* the parent's `MemInv` (memory side `MemOKP`, `Inh`, `PubCpl`): the parent has no promises, so its
  `MemOKP` covers every message at a shared label, foreign promises included;
* the observer clauses `ObsAll` (`PubDefP`/`PubPair`/`PubLive` at the fresh index `n`);
* the global `BoxTopG`, `SharedTyOK`, and an unborn-stripe hypothesis `hU` for the kid's fresh labels.

`MemInv` never reads the cut's `fp`, so the lemma holds at any `fpOf` (`memInv_kidM`).
-/

namespace TermSpawnKidMem
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
  TermMain TermSpawn
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A cell of the kid's cut is a shared cell of the global environment (the kid owns nothing). -/
theorem cutSto_kid {Eg : GEnv} {c : Cfg} (hOL : OwnLive Eg c) {l : AllocLabel} {cl : Cell}
    (h : cutSto Eg c.ths.size l = some cl) : Eg.sto l = some cl ∧ Eg.Shared l := by
  obtain ⟨hs, ho⟩ := cutSto_some.1 h
  rcases ho with ho | hsh
  · have := hOL.1 l cl c.ths.size hs ho; omega
  · exact ⟨hs, hsh⟩

theorem cutSto_kid_own {Eg : GEnv} {c : Cfg} (hOL : OwnLive Eg c) {l : AllocLabel} {cl : Cell}
    (h : cutSto Eg c.ths.size l = some cl) : cl.owner ≠ some c.ths.size := by
  intro ho
  have := hOL.1 l cl c.ths.size (cutSto_sub h) ho; omega

/-- **The kid's memory invariant** at `Cut Eg n ∅`. -/
theorem memInv_kidM0 {g0 g : G} {c : Cfg} {th kid : TTh} {Eg : GEnv} {i : Nat} {S0 : AllocLabel → Prop}
    (hM : MemInv g0 (Cut Eg i S0) (stOf c.mem c.pairs th)) (hnp : th.promises = [])
    (hOL : OwnLive Eg c) (hsh : SharedTyOK Eg) (hbs : ∀ l B, Eg.box l = some B → Eg.sto l = none)
    (hbt : BoxTopG Eg c) (hObs : ObsAll Eg c)
    (hU : ∀ q, Eg.sto (freshLabel g.lbase g.n g.i q) = none ∧ Eg.box (freshLabel g.lbase g.n g.i q) = none ∧
      Eg.ini (freshLabel g.lbase g.n g.i q) = 0 ∧ Eg.pfr (freshLabel g.lbase g.n g.i q) = none ∧
      ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → m.loc.label ≠ freshLabel g.lbase g.n g.i q)
    (hp2 : kid.promises = []) (hn2 : kid.nalloc = 0) :
    MemInv g (Cut Eg c.ths.size (fun _ => False)) (stOf c.mem c.pairs kid) := by
  have hs : stOf c.mem c.pairs kid = ⟨c.mem, c.pairs, kid.vs, [], 0, kid.undefs⟩ := by
    simp [stOf, hp2, hn2]
  rw [hs]
  obtain ⟨h1M, -, -, -, -, -, -, -, ⟨-, hInh, hCpl, -⟩, ⟨-, -, hB3⟩, -⟩ := hM
  have hI := InclS_cut Eg i c.ths.size S0 (fun _ => False)
  have hP0 : (stOf c.mem c.pairs th).promises = [] := hnp
  obtain ⟨hD, hPP, hPL⟩ := hObs c.ths.size (Nat.le_refl _)
  refine ⟨⟨fun t m cl ht hm hc => ?_, fun t m0 m1 cl ht h0 h1' hc => ?_, h1M.2.2⟩, fun l cl hc ho => ?_,
    fun t ht => ?_, ⟨fun k _ => ?_, fun t m _ _ hPU => ?_⟩, fun l hl => hl.elim, ⟨fun l cl hc ho => ?_, fun l cl hc ho => ?_⟩,
    ?_, fun l cl f hc ho => ?_, ⟨fun l hl => hl.elim, fun l cl b S us hc hS hu hi => ?_, fun l cl f hc hf => ?_, hPP, hPL⟩,
    ⟨fun k _ => ?_, ?_, fun l B hB => ?_⟩, ⟨List.nodup_nil, fun t ht => ?_, fun t ht => ?_⟩⟩
  · obtain ⟨hs1, hsh1⟩ := cutSto_kid hOL hc
    have hc0 : cutSto Eg i m.loc.label = some cl := cutSto_shared hs1 hsh1
    rcases h1M.1 t m cl (by rw [hP0]; exact List.not_mem_nil) hm hc0 with h | h
    · exact .inl h
    · exact .inr (WordOK_transferS hI (hsh _ cl hsh1 hs1) h)
  · obtain ⟨hs1, hsh1⟩ := cutSto_kid hOL hc
    have hc0 : cutSto Eg i m0.loc.label = some cl := cutSto_shared hs1 hsh1
    exact PairOK_transferS hI (hsh _ cl hsh1 hs1) (h1M.2.1 t m0 m1 cl ht h0 h1' hc0)
  · exact absurd ho (cutSto_kid_own hOL hc)
  · cases ht
  · obtain ⟨g1, g2, g3, g4, g5⟩ := hU k
    refine ⟨?_, fun t m hm hl => ?_, ?_, ?_⟩
    · show cutSto Eg c.ths.size _ = none
      unfold cutSto; simp [GEnv.InCut, g1]
    · exact absurd hl (g5 t m hm)
    · exact g3
    · exact g4
  · obtain ⟨cl, -, -, -, hc, ho, -⟩ := hPU
    exact absurd ho (cutSto_kid_own hOL hc)
  · exact absurd ho (cutSto_kid_own hOL hc)
  · exact absurd ho (cutSto_kid_own hOL hc)
  · exact hD
  · exact absurd ho (cutSto_kid_own hOL hc)
  · obtain ⟨hs1, hsh1⟩ := cutSto_kid hOL hc
    have hc0 : cutSto Eg i l = some cl := cutSto_shared hs1 hsh1
    obtain ⟨ws, hv, hl⟩ := hInh l cl b S us hc0 hS hu hi
    exact ⟨ws, ValOf_transferS hI (noOR_seg hS (hsh _ cl hsh1 hs1)) hv, hl⟩
  · obtain ⟨hs1, hsh1⟩ := cutSto_kid hOL hc
    exact hCpl l cl f (cutSto_shared hs1 hsh1) hf
  · exact (hU k).2.1
  · exact BoxTopP_of_G hbt (fun t ht => by cases ht)
  · refine ⟨?_, (hB3 l B hB).2.1, fun hl => hl.elim⟩
    show cutSto Eg c.ths.size l = none
    unfold cutSto; simp [GEnv.InCut, hbs l B hB]
  · cases ht
  · cases ht

/-- The cut at an updated `fpOf` is the cut with that `fp`. -/
theorem cut_withFp (Eg : GEnv) (F : Nat → List Ts) (i : Nat) (S : AllocLabel → Prop) :
    Cut { Eg with fpOf := F } i S = { Cut Eg i S with fp := F i } := by
  have : cutSto { Eg with fpOf := F } i = cutSto Eg i := by
    funext l; unfold cutSto GEnv.InCut GEnv.Shared; rfl
  simp only [Cut, this]

/-- `ValOf` does not read `fp`. -/
theorem valOf_fp (E : TEnv) (x : List Ts) : ValOf { E with fp := x } = ValOf E := by
  funext T ws; apply propext
  constructor
  · intro h
    exact ⟨VR_mono T (CE ({ E with fp := x } : TEnv).unsee) (CE E.unsee) _ _ _ (fun _ _ _ h => h)
      (fun _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
      (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h) (fun _ _ h => h) h.1 (fun _ => Nat.le_refl _), h.2⟩
  · intro h
    exact ⟨VR_mono T (CE E.unsee) (CE ({ E with fp := x } : TEnv).unsee) _ _ _ (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
      (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h) (fun _ _ h => h) h.1 (fun _ => Nat.le_refl _), h.2⟩

/-- `MemInv` does not read the cut's `fp`. -/
theorem memInv_withFp {g : G} {E : TEnv} {s : St} (x : List Ts) (h : MemInv g E s) :
    MemInv g { E with fp := x } s := by
  simp only [MemInv, MemOKP, OwnOKPF, OwnHidP, PubDefP, HiddenP, PubInv, PubCpl, Inh, BoxInv, OwnPubV,
    OwnOKSF, OwnPairF, LatestSF, TypedAt, CellOK, BufOK, PubMem, PubPair, WordOK, PairOK, ValOfS, valOf_fp]
  exact h

theorem pub3_withFp {E : TEnv} {mem : Memory} {pairs : List Ts} (x : List Ts)
    (h : PubDefP E mem [] ∧ PubPair E mem pairs [] ∧ PubLive E mem) :
    PubDefP { E with fp := x } mem [] ∧ PubPair { E with fp := x } mem pairs [] ∧ PubLive { E with fp := x } mem := by
  simp only [PubDefP, HiddenP, PubPair, PubLive, WordOK, PairOK, ValOfS, valOf_fp]
  exact h

/-- **The kid's memory invariant at any foreign-promise ghost** `F` (`MemInv` does not read `fp`). -/
theorem memInv_kidM {g0 g : G} {c : Cfg} {th kid : TTh} {Eg : GEnv} {i : Nat} {S0 : AllocLabel → Prop}
    (F : Nat → List Ts)
    (hM : MemInv g0 (Cut Eg i S0) (stOf c.mem c.pairs th)) (hnp : th.promises = [])
    (hOL : OwnLive Eg c) (hsh : SharedTyOK Eg) (hbs : ∀ l B, Eg.box l = some B → Eg.sto l = none)
    (hbt : BoxTopG Eg c) (hObs : ObsAll Eg c)
    (hU : ∀ q, Eg.sto (freshLabel g.lbase g.n g.i q) = none ∧ Eg.box (freshLabel g.lbase g.n g.i q) = none ∧
      Eg.ini (freshLabel g.lbase g.n g.i q) = 0 ∧ Eg.pfr (freshLabel g.lbase g.n g.i q) = none ∧
      ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → m.loc.label ≠ freshLabel g.lbase g.n g.i q)
    (hp2 : kid.promises = []) (hn2 : kid.nalloc = 0) :
    MemInv g (Cut { Eg with fpOf := F } c.ths.size (fun _ => False)) (stOf c.mem c.pairs kid) := by
  have h := memInv_kidM0 (Eg := Eg) (g := g) (kid := kid) hM hnp hOL hsh hbs hbt hObs hU hp2 hn2
  rw [cut_withFp]; exact memInv_withFp _ h

/-- **`ObsAll` after the spawn**: memory is unchanged and the observer indices only shrink. -/
theorem obsAll_kid {Eg : GEnv} {c c' : Cfg} (F : Nat → List Ts) (h : ObsAll Eg c) (hmem : c'.mem = c.mem)
    (hpairs : c'.pairs = c.pairs) (hsz : c.ths.size ≤ c'.ths.size) : ObsAll { Eg with fpOf := F } c' := by
  intro j hj
  rw [hmem, hpairs]
  rw [cut_withFp]; exact pub3_withFp _ (h j (Nat.le_trans hsz hj))

#print axioms TermSpawnKidMem.cutSto_kid
#print axioms TermSpawnKidMem.cutSto_kid_own
#print axioms TermSpawnKidMem.cut_withFp
#print axioms TermSpawnKidMem.valOf_fp
#print axioms TermSpawnKidMem.memInv_withFp
#print axioms TermSpawnKidMem.pub3_withFp
end TermSpawnKidMem

#print axioms TermSpawnKidMem.memInv_kidM0
#print axioms TermSpawnKidMem.memInv_kidM
#print axioms TermSpawnKidMem.obsAll_kid
