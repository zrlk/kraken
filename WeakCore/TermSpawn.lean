import WeakCore.TermSpawnDefs
import WeakCore.TermKidLabel
/-!
# TermSpawn — the spawn lemma `startOK_spawnS`
-/
namespace TermSpawn
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## The shape of `spawnS` -/

section shape
variable {cs : Cfg} {th : TTh} {res : List Word} {kids : List Kid}

theorem spawnS_eq (hth : cs.ths[0]? = some th) :
    spawnS cs res kids =
      { mem := cs.mem
        pairs := cs.pairs
        ths := (kids.map (kidTh th.vs res)).toArray
        lbase := cs.lbase + cs.n * th.nalloc
        boxFence := cs.boxFence } := by
  simp [spawnS, hth]

theorem spawnS_mem (hth : cs.ths[0]? = some th) : (spawnS cs res kids).mem = cs.mem := by rw [spawnS_eq hth]
theorem spawnS_pairs (hth : cs.ths[0]? = some th) : (spawnS cs res kids).pairs = cs.pairs := by rw [spawnS_eq hth]
theorem spawnS_lbase (hth : cs.ths[0]? = some th) : (spawnS cs res kids).lbase = cs.lbase + cs.n * th.nalloc := by
  rw [spawnS_eq hth]
/-- (M0) At width `1` the spawn base is the old `cs.lbase + th.nalloc` (propositionally, `Nat.one_mul`). -/
theorem spawnS_lbase_n1 (hth : cs.ths[0]? = some th) (hn1 : cs.n = 1) :
    (spawnS cs res kids).lbase = cs.lbase + th.nalloc := by
  rw [spawnS_lbase hth, hn1, Nat.one_mul]
theorem spawnS_bf (hth : cs.ths[0]? = some th) : (spawnS cs res kids).boxFence = cs.boxFence := by rw [spawnS_eq hth]
theorem spawnS_size (hth : cs.ths[0]? = some th) : (spawnS cs res kids).ths.size = kids.length := by
  rw [spawnS_eq hth]; simp
theorem spawnS_n (hth : cs.ths[0]? = some th) : (spawnS cs res kids).n = kids.length := by
  rw [spawnS_eq hth]; simp [Cfg.n]
theorem spawnS_get (hth : cs.ths[0]? = some th) (i : Nat) :
    (spawnS cs res kids).ths[i]? = kids[i]?.map (kidTh th.vs res) := by
  rw [spawnS_eq hth]; simp

/-- Every thread of the spawn is a kid's start thread. -/
theorem spawnS_th (hth : cs.ths[0]? = some th) {i : Nat} {t : TTh} (h : (spawnS cs res kids).ths[i]? = some t) :
    ∃ kd, kids[i]? = some kd ∧ t = kidTh th.vs res kd := by
  rw [spawnS_get hth] at h
  cases e : kids[i]? with
  | none => rw [e] at h; cases h
  | some kd => rw [e] at h; cases h; exact ⟨kd, rfl, rfl⟩

theorem spawnS_noProm (hth : cs.ths[0]? = some th) : AllNoProm (spawnS cs res kids) := by
  intro i t h
  obtain ⟨kd, -, rfl⟩ := spawnS_th hth h
  rfl

theorem tminOf_noProm {sto : TermPtrRts.Sto} {mem : Memory} {ps : List Ts} {t : TTh} (h : t.promises = [])
    (a : AllocLabel) : TermPtrRts.tminOf sto (stOf mem ps t) a = none := by
  unfold TermPtrRts.tminOf; rw [show (stOf mem ps t).promises = [] from h]; rfl

theorem tminG_spawnS (hth : cs.ths[0]? = some th) (Eg : GEnv) (j : Nat) (a : AllocLabel) :
    TermPtrRts.tminG Eg (spawnS cs res kids) j a = none := by
  unfold TermPtrRts.tminG; rw [spawnS_get hth]
  cases kids[j]? with
  | none => rfl
  | some kd => exact tminOf_noProm rfl a

end shape

/-! ## The ghost reshape -/

/-- (J-a) **Ghost owners are live threads**: carried along the setup run (scratch copies of
`sysInv_thread`/`sysInv_prom`); the clean-start lemma gives it initially. -/
def OwnLive (Eg : GEnv) (c : Cfg) : Prop :=
  (∀ l cl i, Eg.sto l = some cl → cl.owner = some i → i < c.ths.size) ∧
    ∀ l B, Eg.box l = some B → B.own < c.ths.size

/-- The spawned global environment: no foreign promises. -/
def EgS (Eg : GEnv) : GEnv := { Eg with fpOf := fun _ => [] }

theorem allProms_nil_of {c : Cfg} (h : AllNoProm c) : allProms c = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro t ht
  exact TermInit.allProms_nil h t ht

theorem fpOf0_nil {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {th : TTh}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hnp : AllNoProm c) (hth : c.ths[0]? = some th) :
    Eg.fpOf 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro t ht
  have := (hN.proms 0 th hth t).1 (List.mem_append_right _ ht)
  rw [allProms_nil_of hnp] at this
  cases this

/-- Thread `0`'s cut is unchanged by the reshape. -/
theorem cut_EgS0 {Eg : GEnv} (h : Eg.fpOf 0 = []) (S : AllocLabel → Prop) : Cut (EgS Eg) 0 S = Cut Eg 0 S := by
  unfold Cut; rw [show (EgS Eg).fpOf 0 = Eg.fpOf 0 by rw [h]; rfl]; rfl

/-- A kid's start thread has no promises. -/
@[simp] theorem kidTh_promises (vs : VState) (res : List Word) (kd : Kid) : (kidTh vs res kd).promises = [] := rfl
@[simp] theorem kidTh_vs (vs : VState) (res : List Word) (kd : Kid) : (kidTh vs res kd).vs = vs := rfl
@[simp] theorem kidTh_nalloc (vs : VState) (res : List Word) (kd : Kid) : (kidTh vs res kd).nalloc = 0 := rfl

/-- Thread `i`'s frame total after the spawn: the setup's at `0`, nothing elsewhere. -/
def at0 (f : Nat → Res) : Nat → Res := fun i => if i = 0 then f 0 else .zero

/-! ## Sums over the spawned threads -/

theorem rsum_zero {α : Type} (g : α → Res) : ∀ (L : List α), (∀ x ∈ L, g x = .zero) → Res.sum (L.map g) = .zero
  | [], _ => rfl
  | x :: L, h => by
      rw [List.map_cons, Res.sum_cons, h x (List.mem_cons_self ..), rsum_zero g L (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      exact Res.add_zero _

theorem rsum_at0 {n : Nat} (hn : 1 ≤ n) (f : Nat → Res) (hf : ∀ i, i ≠ 0 → f i = .zero) :
    Res.sum ((List.range n).map f) = f 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map, List.map_cons, Res.sum_cons, List.map_map,
    rsum_zero (f ∘ Nat.succ) _ (fun x _ => hf _ (Nat.succ_ne_zero x))]
  exact Res.add_zero _

theorem nsum_zero {α : Type} (g : α → Nat) : ∀ (L : List α), (∀ x ∈ L, g x = 0) → (L.map g).sum = 0
  | [], _ => rfl
  | x :: L, h => by
      rw [List.map_cons, List.sum_cons, h x (List.mem_cons_self ..), nsum_zero g L (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem nsum_at0 {n : Nat} (hn : 1 ≤ n) (f : Nat → Nat) (hf : ∀ i, i ≠ 0 → f i = 0) :
    ((List.range n).map f).sum = f 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
    nsum_zero (f ∘ Nat.succ) _ (fun x _ => hf _ (Nat.succ_ne_zero x))]
  rfl

theorem at0_ne {f : Nat → Res} {i : Nat} (h : i ≠ 0) : at0 f i = .zero := by simp [at0, h]
@[simp] theorem at0_zero (f : Nat → Res) : at0 f 0 = f 0 := rfl

/-- The spawned threads' labels: the setup's fresh labels from its allocation count on. -/
theorem freshLabel_spawn (b na n q j : Nat) : freshLabel (b + na) n q j = freshLabel b 1 0 (na + q + n * j) := by
  show b + na + q + n * j = b + 0 + 1 * (na + q + n * j)
  rw [Nat.one_mul]; omega

/-- (M0) A property of thread `0`'s labels from its count on and of the unborn stripes `[1, cs.n)`
holds at every kid label (`kidLabel_of`: the kid base is `cs.lbase + cs.n * th.nalloc`). -/
theorem kidP {cs : Cfg} {th : TTh} {res : List Word} {kids : List Kid} {P : AllocLabel → Prop}
    (h1 : cs.ths.size = 1) (hth : cs.ths[0]? = some th)
    (h0 : ∀ k, th.nalloc ≤ k → P (freshLabel cs.lbase cs.n 0 k))
    (hU : ∀ r s, 0 < r → r < cs.n → P (freshLabel cs.lbase cs.n r s)) (L q j : Nat) :
    P (freshLabel (spawnS cs res kids).lbase L q j) := by
  rw [spawnS_lbase hth]
  exact kidLabel_of (by have := cs.size_le_n; omega) h0 hU L q j

/-- A `FreshX` label is globally fresh for any thread. -/
theorem gFreshL_of_X {Eg : GEnv} {c : Cfg} {th : TTh} {l : AllocLabel} (h : FreshX Eg c l) : GFreshL Eg c th l :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun t m hm hl => absurd hl (h.2.2.2.2 t m hm)⟩

/-- (M0) Every kid label is globally fresh (thread `0`'s `fresh` and the unborn stripes' `freshU`). -/
theorem kidG {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {cs : Cfg} {th : TTh} {res : List Word} {kids : List Kid}
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init MintOK cs Eg Tot HP HS cr db) (h1 : cs.ths.size = 1) (hth : cs.ths[0]? = some th)
    (L q j : Nat) : GFreshL Eg cs th (freshLabel (spawnS cs res kids).lbase L q j) :=
  kidP h1 hth (fun k hk => hN.fresh 0 th hth k hk)
    (fun r s hr hrn => gFreshL_of_X (hN.freshU r s (by omega) hrn).1) L q j

/-- (M0) No own key of a kid label is held (thread `0`'s `ownF` and the unborn stripes' `freshU`). -/
theorem kidOwn {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {cs : Cfg} {th : TTh} {res : List Word} {kids : List Kid}
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init MintOK cs Eg Tot HP HS cr db) (h1 : cs.ths.size = 1) (hth : cs.ths[0]? = some th)
    (L q j : Nat) : OwnZ cs Tot HP HS cr (freshLabel (spawnS cs res kids).lbase L q j) :=
  kidP h1 hth (fun k hk => hN.ownF 0 th k hth hk) (fun r s hr hrn => (hN.freshU r s (by omega) hrn).2) L q j

theorem PromAtG_nil {Eg : GEnv} {c : Cfg} (h : allProms c = []) (a : Address) : PromAtG Eg c a = [] := by
  unfold PromAtG; rw [h]; simp

theorem thSum_one (F : Nat → Res) : thSum 1 F = F 0 := by simp [thSum]

/-! ## Child `0`'s memory invariant -/

/-- The setup thread's memory invariant, at a thread with its views, no promises and no allocations,
under a `G` whose fresh labels are among the setup's. -/
theorem memInv_child0 {g0 g : G} {E : TEnv} {mem : Memory} {pairs : List Ts} {th th2 : TTh}
    (hM : MemInv g0 E (stOf mem pairs th)) (hnp : th.promises = []) (hvs : th2.vs = th.vs)
    (hp2 : th2.promises = []) (hn2 : th2.nalloc = 0)
    (hfl : ∀ j, (E.sto (freshLabel g.lbase g.n g.i j) = none ∧
      (∀ (t : Nat) (m : Msg), mem[t]? = some m → m.loc.label = freshLabel g.lbase g.n g.i j → t ∈ th.promises) ∧
      E.ini (freshLabel g.lbase g.n g.i j) = 0 ∧ E.pfr (freshLabel g.lbase g.n g.i j) = none) ∧
      E.box (freshLabel g.lbase g.n g.i j) = none) :
    MemInv g E (stOf mem pairs th2) := by
  have hs : stOf mem pairs th2 = { stOf mem pairs th with nalloc := 0, undefs := th2.undefs } := by
    simp [stOf, hvs, hp2, hnp, hn2]
  rw [hs]
  obtain ⟨h1, h2, h3, ⟨-, hPC⟩, h5, h6, h7, h8, h9, ⟨-, hB2, hB3⟩, h11⟩ := hM
  exact ⟨h1, h2, h3, ⟨fun j _ => (hfl j).1, hPC⟩, h5, h6, h7, h8, h9, ⟨fun j _ => (hfl j).2, hB2, hB3⟩, h11⟩

/-- **Child `0`'s `ThSys`**, from the setup thread's, given the frame typing of the kid at the
setup's cut (`hty`; the entry typing, built separately). -/
theorem thSys_child0 {p : Prog} {k : Promises.Knobs} {arch : Arch} {cs : Cfg} {th th2 : TTh} {res : List Word}
    {kids : List Kid} {Eg : GEnv} {T H HS : Res} {cr db : Ts → Res}
    (hT : ThSys p (gOf p k arch cs 0) cs.mem cs.pairs th Eg T H HS cr db) (hnp : th.promises = [])
    (h1 : cs.ths.size = 1) (hth : cs.ths[0]? = some th) (hfp : Eg.fpOf 0 = [])
    (hG : ∀ j, GFreshL Eg cs th (freshLabel (spawnS cs res kids).lbase (spawnS cs res kids).n 0 j))
    (hvs : th2.vs = th.vs) (hp2 : th2.promises = []) (hn2 : th2.nalloc = 0)
    (hty : ∀ S, MemInv (gOf p k arch cs 0) (Cut Eg 0 S) (stOf cs.mem cs.pairs th) →
      ThInvRE p (Cut Eg 0 S) th T → ThInvRE p (Cut Eg 0 S) th2 T ∧ ThInvE p (Cut Eg 0 S) th2) :
    ThSys p (gOf p k arch (spawnS cs res kids) 0) (spawnS cs res kids).mem (spawnS cs res kids).pairs th2 (EgS Eg)
      T H HS (fun _ => .zero) (fun _ => .zero) := by
  obtain ⟨S, hRE, -, hM, hP, hS, -⟩ := hT
  have hs : stOf cs.mem cs.pairs th2 = { stOf cs.mem cs.pairs th with nalloc := 0, undefs := th2.undefs } := by
    simp [stOf, hvs, hp2, hnp, hn2]
  obtain ⟨hR2, hE2⟩ := hty S hM hRE
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ThInvRE p (Cut (EgS Eg) 0 S) th2 T
    rw [cut_EgS0 hfp]; exact hR2
  · show ThInvE p (Cut (EgS Eg) 0 S) th2
    rw [cut_EgS0 hfp]; exact hE2
  · show MemInv _ (Cut (EgS Eg) 0 S) _
    rw [cut_EgS0 hfp, spawnS_mem hth, spawnS_pairs hth]
    refine memInv_child0 hM hnp hvs hp2 hn2 (fun j => ?_)
    obtain ⟨g1, g2, g3, g4, g5⟩ := hG j
    refine ⟨⟨?_, fun t m hm hl => g5 t m hm hl, g3, g4⟩, g2⟩
    show cutSto Eg 0 (freshLabel (spawnS cs res kids).lbase (spawnS cs res kids).n 0 j) = none
    cases e : cutSto Eg 0 (freshLabel (spawnS cs res kids).lbase (spawnS cs res kids).n 0 j) with
    | none => rfl
    | some c0 => have h0 := cutSto_sub e; rw [g1] at h0; cases h0
  · show MemHeldP (Cut (EgS Eg) 0 S) _ H
    rw [cut_EgS0 hfp, spawnS_mem hth, spawnS_pairs hth, hs]; exact hP
  · show MemHeldS (Cut (EgS Eg) 0 S) _ HS
    rw [cut_EgS0 hfp, spawnS_mem hth, spawnS_pairs hth, hs]; exact hS
  · intro tw htw
    simp [stOf, hp2] at htw

/-! ## Children `j ≥ 1`: memory side -/

/-- A label in an observer's cut (no cell of its own) is a shared cell, in thread `0`'s cut too. -/
theorem cutSto_obs {Eg : GEnv} {cs : Cfg} {j : Nat} (hOL : OwnLive Eg cs) (h1 : cs.ths.size = 1) (hj : j ≠ 0)
    {l : AllocLabel} {c : Cell} (h : cutSto (EgS Eg) j l = some c) :
    Eg.sto l = some c ∧ Eg.Shared l ∧ cutSto (EgS Eg) 0 l = some c := by
  obtain ⟨hs, ho⟩ := cutSto_some.1 h
  rcases ho with ho | hsh
  · have := hOL.1 l c j hs ho; omega
  · exact ⟨hs, hsh, cutSto_shared (Eg := EgS Eg) hs hsh⟩

/-- No cell of an observer's cut is its own. -/
theorem cutSto_obs_own {Eg : GEnv} {cs : Cfg} {j : Nat} (hOL : OwnLive Eg cs) (h1 : cs.ths.size = 1) (hj : j ≠ 0)
    {l : AllocLabel} {c : Cell} (h : cutSto (EgS Eg) j l = some c) : c.owner ≠ some j := by
  intro ho
  have := hOL.1 l c j (cutSto_sub h) ho; omega

/-- **A child `j ≥ 1`'s memory invariant**: from thread `0`'s, the global clauses, and the observer
clauses `PubDefP`/`PubPair`/`PubLive` carried along the setup run (`TermInterfObs`). -/
theorem memInv_kid {g0 g : G} {cs : Cfg} {th th2 : TTh} {Eg : GEnv} {S0 : AllocLabel → Prop} {j : Nat}
    (hM : MemInv g0 (Cut (EgS Eg) 0 S0) (stOf cs.mem cs.pairs th)) (hnp : th.promises = [])
    (hOL : OwnLive Eg cs) (h1 : cs.ths.size = 1) (hj : j ≠ 0)
    (hsh : SharedTyOK Eg) (hbs : ∀ l B, Eg.box l = some B → Eg.sto l = none)
    (hGK : ∀ k, GFreshL Eg cs th (freshLabel g.lbase g.n g.i k))
    (hbt : BoxTopG Eg cs)
    (hvs : th2.vs = th.vs) (hp2 : th2.promises = []) (hn2 : th2.nalloc = 0)
    (hD : PubDefP (Cut (EgS Eg) j (fun _ => False)) cs.mem [])
    (hPP : PubPair (Cut (EgS Eg) j (fun _ => False)) cs.mem cs.pairs [])
    (hPL : PubLive (Cut (EgS Eg) j (fun _ => False)) cs.mem) :
    MemInv g (Cut (EgS Eg) j (fun _ => False)) (stOf cs.mem cs.pairs th2) := by
  have hs : stOf cs.mem cs.pairs th2 = ⟨cs.mem, cs.pairs, th.vs, [], 0, th2.undefs⟩ := by
    simp [stOf, hvs, hp2, hn2]
  rw [hs]
  obtain ⟨h1M, -, -, -, -, -, -, -, ⟨-, hInh, hCpl, -⟩, ⟨-, -, hB3⟩, -⟩ := hM
  have hI := InclS_cut (EgS Eg) 0 j S0 (fun _ => False)
  have hP0 : (stOf cs.mem cs.pairs th).promises = [] := hnp
  refine ⟨⟨fun t m c ht hm hc => ?_, fun t m0 m1 c ht h0 h1' hc => ?_, h1M.2.2⟩, fun l c hc ho => ?_,
    fun t ht => ?_, ⟨fun k _ => ?_, fun t m _ _ hU => ?_⟩, fun l hl => hl.elim, ⟨fun l c hc ho => ?_, fun l c hc ho => ?_⟩,
    ?_, fun l c f hc ho => ?_, ⟨fun l hl => hl.elim, fun l c b S us hc hS hu hi => ?_, fun l c f hc hf => ?_, hPP, hPL⟩,
    ⟨fun k _ => ?_, ?_, fun l B hB => ?_⟩, ⟨List.nodup_nil, fun t ht => ?_, fun t ht => ?_⟩⟩
  · obtain ⟨hs1, hsh1, hc0⟩ := cutSto_obs hOL h1 hj hc
    rcases h1M.1 t m c (by rw [hP0]; exact List.not_mem_nil) hm hc0 with h | h
    · exact .inl h
    · exact .inr (WordOK_transferS hI (hsh _ c hsh1 hs1) h)
  · obtain ⟨hs1, hsh1, hc0⟩ := cutSto_obs hOL h1 hj hc
    exact PairOK_transferS hI (hsh _ c hsh1 hs1) (h1M.2.1 t m0 m1 c ht h0 h1' hc0)
  · exact absurd ho (cutSto_obs_own hOL h1 hj hc)
  · cases ht
  · obtain ⟨g1, g2, g3, g4, g5⟩ := hGK k
    refine ⟨?_, fun t m hm hl => ?_, ?_, ?_⟩
    · show cutSto (EgS Eg) j _ = none
      unfold cutSto; simp [GEnv.InCut, EgS, g1]
    · have := g5 t m hm hl; rw [hnp] at this; cases this
    · show Eg.ini _ = 0
      exact g3
    · show Eg.pfr _ = none
      exact g4
  · obtain ⟨c, -, -, -, hc, ho, -⟩ := hU
    exact absurd ho (cutSto_obs_own hOL h1 hj hc)
  · exact absurd ho (cutSto_obs_own hOL h1 hj hc)
  · exact absurd ho (cutSto_obs_own hOL h1 hj hc)
  · exact hD
  · exact absurd ho (cutSto_obs_own hOL h1 hj hc)
  · obtain ⟨hs1, hsh1, hc0⟩ := cutSto_obs hOL h1 hj hc
    obtain ⟨ws, hv, hl⟩ := hInh l c b S us hc0 hS hu hi
    exact ⟨ws, ValOf_transferS hI (noOR_seg hS (hsh _ c hsh1 hs1)) hv, hl⟩
  · obtain ⟨hs1, hsh1, hc0⟩ := cutSto_obs hOL h1 hj hc
    exact hCpl l c f hc0 hf
  · show Eg.box _ = none
    exact (hGK k).2.1
  · exact BoxTopP_of_G hbt (fun t ht => by cases ht)
  · refine ⟨?_, (hB3 l B hB).2.1, fun hl => hl.elim⟩
    show cutSto (EgS Eg) j l = none
    unfold cutSto; simp [GEnv.InCut, EgS, hbs l B hB]
  · cases ht
  · cases ht

/-- The global shared holding after the spawn. -/
theorem memHeldG_spawnS {cs : Cfg} {th : TTh} {res : List Word} {kids : List Kid} {Eg : GEnv} {HS : Res}
    (hH : MemHeldG Eg cs HS) (hnp : AllNoProm cs) (hth : cs.ths[0]? = some th) :
    MemHeldG (EgS Eg) (spawnS cs res kids) HS := by
  obtain ⟨L, Rl, e1, e2, e3, e4, e5⟩ := hH
  refine ⟨L, Rl, e1, e2, e3, e4, fun l hl => ⟨(e5 l hl).1, fun cl hcl => ?_⟩⟩
  obtain ⟨vals, hv, hc⟩ := (e5 l hl).2 cl hcl
  refine ⟨vals, fun o w ho => ?_, hc⟩
  rw [PromAtG_nil (allProms_nil_of (spawnS_noProm hth)), spawnS_mem hth]
  have := hv o w ho
  rwa [PromAtG_nil (allProms_nil_of hnp)] at this

/-- Observer clauses read the same at `EgS Eg` (only the foreign-promise lists differ). -/
theorem InclS_cut_EgS (Eg : GEnv) (i j : Nat) (S S' : AllocLabel → Prop) : InclS (Cut Eg i S) (Cut (EgS Eg) j S') :=
  ⟨rfl, fun _ _ f hc hf => cutSto_shared (Eg := EgS Eg) (cutSto_sub hc) ⟨f, hf⟩, fun _ => Nat.le_refl _,
    fun _ _ h => h, fun _ _ h => h, fun _ => Nat.le_refl _⟩

theorem cutSto_EgS {Eg : GEnv} {j : Nat} {l : AllocLabel} {c : Cell} (h : cutSto (EgS Eg) j l = some c) :
    cutSto Eg j l = some c := by
  obtain ⟨h1, h2⟩ := cutSto_some.1 h
  exact cutSto_some.2 ⟨h1, h2⟩

theorem pubDefP_EgS {Eg : GEnv} {j : Nat} {S : AllocLabel → Prop} {mem : Memory} (hsh : SharedTyOK Eg)
    (h : PubDefP (Cut Eg j S) mem []) : PubDefP (Cut (EgS Eg) j S) mem [] := by
  intro l c f hc ho hf o hio
  have hc' := cutSto_EgS hc
  exact TermInterf.HiddenP_conv (fun t m ht => by cases ht)
    (fun w hw => WordOK_transferS (InclS_cut_EgS Eg j j S S) (hsh l c ⟨f, hf⟩ (cutSto_sub hc')) hw)
    (h l c f hc' ho hf o hio)

theorem pubPair_EgS {Eg : GEnv} {j : Nat} {S : AllocLabel → Prop} {mem : Memory} {pairs : List Ts}
    (hsh : SharedTyOK Eg) (h : PubPair (Cut Eg j S) mem pairs []) : PubPair (Cut (EgS Eg) j S) mem pairs [] := by
  intro l c f o hc hg hf hT t0 t1 m0 m1 h0 h1 hm0 hm1 hl0 hl1 hh0 hh1 hps
  have hc' := cutSto_EgS hc
  exact PairOK_transferS (InclS_cut_EgS Eg j j S S) (hsh l c ⟨f, hf⟩ (cutSto_sub hc'))
    (h l c f o hc' hg hf hT t0 t1 m0 m1 h0 h1 hm0 hm1 hl0 hl1 hh0 hh1 hps)

theorem pubLive_EgS {Eg : GEnv} {j : Nat} {S : AllocLabel → Prop} {mem : Memory}
    (h : PubLive (Cut Eg j S) mem) : PubLive (Cut (EgS Eg) j S) mem :=
  fun l c f b S1 us o hc ho hf hs hu hlt => h l c f b S1 us o (cutSto_EgS hc) ho hf hs hu hlt

/-- **A child `j ≥ 1`'s `ThSys`**, given its entry frame typing (`hty`). -/
theorem thSys_kid {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {cs : Cfg} {th th2 : TTh} {res : List Word} {kids : List Kid}
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    (hN : SysInvN p k arch Init MintOK cs Eg Tot HP HS cr db) (hnp : AllNoProm cs) (h1 : cs.ths.size = 1)
    (hth : cs.ths[0]? = some th) (hOL : OwnLive Eg cs) (hj : j ≠ 0)
    (hObs : PubDefP (Cut Eg j (fun _ => False)) cs.mem [] ∧
      PubPair (Cut Eg j (fun _ => False)) cs.mem cs.pairs [] ∧ PubLive (Cut Eg j (fun _ => False)) cs.mem)
    (hvs : th2.vs = th.vs) (hp2 : th2.promises = []) (hn2 : th2.nalloc = 0)
    (hty : ThInvRE p (Cut (EgS Eg) j (fun _ => False)) th2 .zero ∧ ThInvE p (Cut (EgS Eg) j (fun _ => False)) th2) :
    ThSys p (gOf p k arch (spawnS cs res kids) j) (spawnS cs res kids).mem (spawnS cs res kids).pairs th2 (EgS Eg)
      .zero .zero HS (fun _ => .zero) (fun _ => .zero) := by
  have hfp := fpOf0_nil hN hnp hth
  obtain ⟨S0, -, -, hM00, -⟩ := hN.thr 0 th hth
  have hM0 : MemInv (gOf p k arch cs 0) (Cut (EgS Eg) 0 S0) (stOf cs.mem cs.pairs th) := by
    rw [cut_EgS0 hfp]; exact hM00
  refine ⟨fun _ => False, hty.1, hty.2, ?_, ?_, ?_, ?_⟩
  · rw [spawnS_mem hth, spawnS_pairs hth]
    refine memInv_kid hM0 (hnp 0 th hth) hOL h1 hj hN.shty hN.boxSto
      (fun q => kidG hN h1 hth _ j q) hN.boxtop hvs hp2 hn2
      (pubDefP_EgS hN.shty hObs.1) (pubPair_EgS hN.shty hObs.2.1) (pubLive_EgS hObs.2.2)
  · refine ⟨[], fun _ => .zero, List.nodup_nil, ?_, ?_, rfl, ?_⟩
    · intro l c hq _
      obtain ⟨⟨c1, hc1, ho⟩, -⟩ := hq
      exact absurd ho (cutSto_obs_own hOL h1 hj hc1)
    · intro l h; cases h
    · intro l h; cases h
  · refine MemHeldS_of_G (by rw [spawnS_mem hth]; rfl) hN.shty (fun t => ?_) (memHeldG_spawnS hN.held hnp hth)
    rw [allProms_nil_of (spawnS_noProm hth)]
    simp [stOf, hp2, EgS]
  · intro tw htw
    simp [stOf, hp2] at htw

/-- **The spawn lemma, invariant part.** -/
theorem sysInvN_spawnS {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {cs : Cfg} {th : TTh} {res : List Word} {kids : List Kid}
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init MintOK cs Eg Tot HP HS cr db) (hnp : AllNoProm cs) (h1 : cs.ths.size = 1)
    (hth : cs.ths[0]? = some th) (hkids : kids ≠ []) (hOL : OwnLive Eg cs)
    (hObs : ∀ j, j ≠ 0 → PubDefP (Cut Eg j (fun _ => False)) cs.mem [] ∧
      PubPair (Cut Eg j (fun _ => False)) cs.mem cs.pairs [] ∧ PubLive (Cut Eg j (fun _ => False)) cs.mem)
    (hty0 : ∀ kd, kids[0]? = some kd → ∀ S, MemInv (gOf p k arch cs 0) (Cut Eg 0 S) (stOf cs.mem cs.pairs th) →
      ThInvRE p (Cut Eg 0 S) th (Tot 0) →
        ThInvRE p (Cut Eg 0 S) (kidTh th.vs res kd) (Tot 0) ∧ ThInvE p (Cut Eg 0 S) (kidTh th.vs res kd))
    (htyK : ∀ j kd, j ≠ 0 → kids[j]? = some kd →
      ThInvRE p (Cut (EgS Eg) j (fun _ => False)) (kidTh th.vs res kd) .zero ∧
        ThInvE p (Cut (EgS Eg) j (fun _ => False)) (kidTh th.vs res kd))
    (hLbl : ∀ (i : Nat) kd, kids[i]? = some kd → TermPtrRts.EnvLbl (EgS Eg) (kidTh th.vs res kd).env) :
    SysInvN p k arch Init MintOK (spawnS cs res kids) (EgS Eg) (at0 Tot) (at0 HP) HS (fun _ _ => .zero)
      (fun _ _ => .zero) where
  thr := by
    intro i t hi
    obtain ⟨kd, hkd, rfl⟩ := spawnS_th hth hi
    have hfp := fpOf0_nil hN hnp hth
    by_cases h0 : i = 0
    · subst h0
      simp only [at0_zero]
      exact thSys_child0 (hN.thr 0 th hth) (hnp 0 th hth) h1 hth hfp (fun j => kidG hN h1 hth _ 0 j) rfl rfl rfl
        (hty0 kd hkd)
    · rw [at0_ne h0, at0_ne h0]
      exact thSys_kid hN hnp h1 hth hOL h0 (hObs i h0) rfl rfl rfl (htyK i kd h0 hkd)
  held := memHeldG_spawnS hN.held hnp hth
  clo := hN.clo
  cmg := hN.cmg
  shty := hN.shty
  proms := by
    intro i t hi u
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hi
    rw [allProms_nil_of (spawnS_noProm hth)]
    simp [EgS]
  fpok := by
    intro i t S _
    exact ⟨fun u h => by simp [Cut, EgS] at h, fun u _ h => by simp [Cut, EgS] at h⟩
  fresh := by
    intro i t hi j _
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hi
    obtain ⟨f1, f2, f3, f4, f5⟩ := kidG (res := res) (kids := kids) hN h1 hth (spawnS cs res kids).n i j
    refine ⟨f1, f2, f3, f4, fun t m hm hl => ?_⟩
    rw [spawnS_mem hth] at hm
    have := f5 t m hm hl
    rw [hnp 0 th hth] at this
    cases this
  bal := by
    obtain ⟨M, hM, hb⟩ := hN.bal
    refine ⟨M, hM, ?_⟩
    rw [h1, thSum_one, thSum_one, TermInit.pSumAt_init hnp, TermInit.pSumAt_init hnp] at hb
    simp only [TermInit.pSumAt_init (spawnS_noProm hth), spawnS_size hth, thSum]
    rw [rsum_at0 (List.length_pos_iff.2 hkids) _ (fun i hi => by simp [at0_ne hi]),
      rsum_zero _ _ (fun _ _ => rfl)]
    simpa using hb
  knet := by
    intro key hk
    have hb := hN.knet key hk
    unfold KeyNet at hb ⊢
    rw [h1] at hb
    simp only [TermInit.pSumAt_init hnp] at hb
    simp only [TermInit.pSumAt_init (spawnS_noProm hth), spawnS_size hth]
    rw [nsum_at0 (List.length_pos_iff.2 hkids) _ (fun i hi => by simp [at0_ne hi]),
      nsum_zero (fun _ : Nat => Res.zero key) _ (fun _ _ => rfl)]
    simpa using hb
  bf := by rw [spawnS_bf hth]; exact hN.bf
  boxtop := by
    intro l B hB
    rw [allProms_nil_of (spawnS_noProm hth), spawnS_mem hth]
    have := hN.boxtop l B hB
    rwa [allProms_nil_of hnp] at this
  disj := by
    intro i j ti tj u _ hi _ hu
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hi
    cases hu
  fpfree := by
    intro i t u _ hu
    cases hu
  plt := by
    intro i t u hi hu
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hi
    cases hu
  vwr := by
    intro i t hi
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hi
    rw [spawnS_mem hth]; exact hN.vwr 0 th hth
  frle := by rw [spawnS_mem hth]; exact hN.frle
  rle := hN.rle
  zwIni := hN.zwIni
  predHold := by
    intro j t S a hj ⟨cl, hcl, ho⟩ hpd hPU
    have hj0 : j = 0 := by have := hOL.1 _ cl j hcl ho; omega
    subst hj0
    rw [cut_EgS0 (fpOf0_nil hN hnp hth)] at hPU
    obtain ⟨h, -, hh, -⟩ := hN.predHold 0 th S a hth ⟨cl, hcl, ho⟩ hpd hPU
    rw [hnp 0 th hth] at hh
    cases hh
  bnamed := hN.bnamed
  rid := by
    obtain ⟨rc, hr⟩ := hN.rid
    refine ⟨rc, fun n hn key hk => ?_⟩
    have hb := hr n hn key hk
    rw [h1] at hb
    simp only [TermInit.pSumAt_init hnp] at hb
    simp only [TermInit.pSumAt_init (spawnS_noProm hth), spawnS_size hth]
    rw [nsum_at0 (List.length_pos_iff.2 hkids) _ (fun i hi => by simp [at0_ne hi]),
      nsum_zero (fun _ : Nat => Res.zero key) _ (fun _ _ => rfl)]
    simpa using hb
  promIni := by
    intro j t u m hj hu
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hj
    cases hu
  promTy := by
    intro j t u m hj hu
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hj
    cases hu
  promNU := by
    intro j t u m hj hu
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hj
    cases hu
  ownF := by
    intro q t j hq _
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hq
    obtain ⟨hA, hB⟩ := kidOwn (res := res) (kids := kids) hN h1 hth (spawnS cs res kids).n q j
    rw [h1] at hA
    refine ⟨fun n _ => ?_, hB⟩
    rw [TermInit.pSumAt_init (spawnS_noProm hth)]
    by_cases h0 : n = 0
    · subst h0
      have := hA 0 (by omega)
      rw [TermInit.pSumAt_init hnp] at this
      simpa using this
    · simp [at0_ne h0]
  promNoTwo := by
    intro j t u m cl hj hu
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hj
    cases hu
  undefAt := by rw [spawnS_mem hth]; exact hN.undefAt
  ownKeyOwn := by
    intro j t l hj hT
    by_cases h0 : j = 0
    · subst h0
      exact hN.ownKeyOwn 0 th l hth (by simpa [at0] using hT)
    · exact absurd (by simp [at0, h0]) hT
  ownPub := by
    intro l hp
    obtain ⟨h1', h2⟩ := hN.ownPub l hp
    refine ⟨h1', fun hs => ⟨fun j t hj => ?_, (h2 hs).2⟩⟩
    by_cases h0 : j = 0
    · subst h0; simpa [at0] using (h2 hs).1 0 th hth
    · simp [at0, h0]
  boxPV := hN.boxPV
  boxFrOwn := by
    intro l B hB t ht
    have h0 : B.own = 0 := by have := hOL.2 l B hB; omega
    rw [h0] at ht
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth ht
    exact hN.boxFrOwn l B hB th (by rw [h0]; exact hth)
  boxFrLe := by rw [spawnS_mem hth]; exact hN.boxFrLe
  vwrLt := by
    intro i t hi
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hi
    rw [spawnS_mem hth]; exact hN.vwrLt 0 th hth
  boxFrLt := by rw [spawnS_mem hth]; exact hN.boxFrLt
  frlt := by rw [spawnS_mem hth]; exact hN.frlt
  payOwn := hN.payOwn
  boxSto := hN.boxSto
  ownCoh := by
    intro i t S hi
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hi
    by_cases h0 : i = 0
    · subst h0
      rw [cut_EgS0 (fpOf0_nil hN hnp hth)]
      intro l c hc ho hp o ho'
      exact hN.ownCoh 0 th S hth l c hc ho hp o ho'
    · intro l c hc ho
      obtain ⟨-, hc'⟩ := cutSto_some.1 hc
      have := hOL.1 l c i (cutSto_sub hc) ho
      omega
  riniCoh := by
    intro i t S hi
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hi
    by_cases h0 : i = 0
    · subst h0
      rw [cut_EgS0 (fpOf0_nil hN hnp hth), spawnS_mem hth]
      intro tt m c N e us f _ hm hc ho hp
      have hnp0 : tt ∉ (stOf cs.mem cs.pairs th).promises := by
        show tt ∉ th.promises
        rw [hnp 0 th hth]; exact List.not_mem_nil
      exact hN.riniCoh 0 th S hth tt m c N e us f hnp0 hm hc ho hp
    · intro tt m c N e us f _ _ hc ho
      obtain ⟨-, hc'⟩ := cutSto_some.1 hc
      have := hOL.1 _ c i (cutSto_sub hc) ho
      omega
  promInCut := by
    intro j t u m hj hu
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hj
    cases hu
  promClos := by
    intro j t u m hj hu
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hj
    cases hu
  stoNI := hN.stoNI
  stoW := hN.stoW
  undefLow := by rw [spawnS_mem hth]; exact hN.undefLow
  promAbove := by
    intro j t hj u hu
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hj
    cases hu
  msgWords := by intro t m cl hm; rw [spawnS_mem hth] at hm; exact hN.msgWords t m cl hm
  fgnClos := by
    intro j t u m hj hu
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hj
    cases hu
  cellOwn := by
    intro l cl hcl hm
    have hm' : (∃ (t : Nat) (m : Msg), cs.mem[t]? = some m ∧ m.loc.label = l) ∨ Eg.Shared l := by
      rw [spawnS_mem hth] at hm; exact hm
    refine ⟨fun i hi => ?_, (hN.cellOwn l cl hcl hm').2⟩
    have := hOL.1 l cl i hcl hi
    rw [h1] at this
    rw [spawnS_size hth]
    have h0 : i = 0 := by omega
    subst h0
    exact List.length_pos_iff.2 hkids
  ptrGL := fun hk => by
    unfold TermPtrRts.PtrRtsGL
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j t a cl f hj hs ho hp hkey t0 ht
      rw [tminG_spawnS hth] at ht; cases ht
    · intro i t hi
      obtain ⟨kd, hkd, rfl⟩ := spawnS_th hth hi
      exact ⟨hLbl i kd hkd, fun f hf => by cases hf⟩
    · intro j a cl f hs ho hp hkey
      exfalso
      by_cases h0 : j = 0
      · subst h0
        have hT := (hN.ptrGL hk).2.2.1 0 a cl f hs ho hp hkey
        unfold TermPtrRts.tminG at hT; rw [hth] at hT
        exact hT (tminOf_noProm (hnp 0 th hth) a)
      · rw [at0_ne h0, at0_ne h0] at hkey; exact Nat.lt_irrefl 0 hkey
    · intro j t a cl f hj hs ho hp hkey t0 ht
      rw [tminG_spawnS hth] at ht; cases ht
  granW := fun hk => Or.inr (by
    rw [spawnS_mem hth, spawnS_pairs hth]; exact (hN.granW hk).resolve_left (by omega))
  stoLay := hN.stoLay
  boxPlantSep := by
    intro hk l B hB o w hw j t a cl f t0 hj ha ho hf hp ht hn
    rw [tminG_spawnS hth] at ht; cases ht
  fgnCnt := by
    intro _ i t u m hi hu
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hi
    cases hu
  plantIdx := by
    intro hk j t l cl hj hs ho hpf hK
    exfalso
    by_cases h0 : j = 0
    · subst h0
      obtain ⟨t0, mP, -, -, htp, -⟩ := (hN.plantIdx hk) 0 th l cl hth hs ho hpf hK
      rw [hnp 0 th hth] at htp; cases htp
    · unfold TermPlantAtT.KeyG at hK; rw [at0_ne h0, at0_ne h0] at hK; exact Nat.lt_irrefl 0 hK
  pool := by
    refine ⟨fun _ _ => .zero, TermPool.poolTag_zero _ _ (spawnS_noProm hth), TermOverCr.overCrG_noProm (spawnS_noProm hth), ?_, ?_, ?_⟩ <;>
      rw [TermPool.crPl_zero]
    · -- (R4 spawn port) copy of `bal`
      obtain ⟨M, hM, hb⟩ := hN.bal
      refine ⟨M, hM, ?_⟩
      rw [h1, thSum_one, thSum_one, TermInit.pSumAt_init hnp, TermInit.pSumAt_init hnp] at hb
      simp only [TermInit.pSumAt_init (spawnS_noProm hth), spawnS_size hth, thSum]
      rw [rsum_at0 (List.length_pos_iff.2 hkids) _ (fun i hi => by simp [at0_ne hi]),
        rsum_zero _ _ (fun _ _ => rfl)]
      simpa using hb
    · -- copy of `knet`
      intro key hk
      have hb := hN.knet key hk
      unfold KeyNet at hb ⊢
      rw [h1] at hb
      simp only [TermInit.pSumAt_init hnp] at hb
      simp only [TermInit.pSumAt_init (spawnS_noProm hth), spawnS_size hth]
      rw [nsum_at0 (List.length_pos_iff.2 hkids) _ (fun i hi => by simp [at0_ne hi]),
        nsum_zero (fun _ : Nat => Res.zero key) _ (fun _ _ => rfl)]
      simpa using hb
    · -- copy of `rid`
      obtain ⟨rc, hr⟩ := hN.rid
      refine ⟨rc, fun n hn key hk => ?_⟩
      have hb := hr n hn key hk
      rw [h1] at hb
      simp only [TermInit.pSumAt_init hnp] at hb
      simp only [TermInit.pSumAt_init (spawnS_noProm hth), spawnS_size hth]
      rw [nsum_at0 (List.length_pos_iff.2 hkids) _ (fun i hi => by simp [at0_ne hi]),
        nsum_zero (fun _ : Nat => Res.zero key) _ (fun _ _ => rfl)]
      simpa using hb
  cfgCoh := by
    intro i t hi
    obtain ⟨kd, -, rfl⟩ := spawnS_th hth hi
    rw [spawnS_mem hth]
    exact hN.cfgCoh 0 th hth
  freshU := by
    rw [spawnS_n hth]
    exact TermFreshU.freshU_le (Nat.le_of_eq (spawnS_size hth).symm)


#print axioms TermSpawn.sysInvN_spawnS
#print axioms TermSpawn.thSys_kid
#print axioms TermSpawn.thSys_child0
end TermSpawn

#print axioms TermSpawn.spawnS_n
#print axioms TermSpawn.spawnS_lbase_n1
#print axioms TermSpawn.kidP
#print axioms TermSpawn.gFreshL_of_X
#print axioms TermSpawn.kidG
#print axioms TermSpawn.kidOwn
