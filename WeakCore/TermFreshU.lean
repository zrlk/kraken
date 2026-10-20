import WeakCore.TermInterf
import WeakCore.TermOwnFresh
import WeakCore.TermPoolThread
import WeakCore.TermInit
/-!
# TermFreshU — preservation of the M0 clause `freshU`

`TermSys.FreshU c.n Eg c Tot HP HS cr`: every unborn-stripe label `freshLabel lbase c.n q j`
(`ths.size ≤ q < c.n`) is fresh (`FreshX`) and its own key is unheld (`OwnZ`).  Preservation is
label-generic (`freshX_thread`/`ownZ_thread`/`freshX_prom`/`ownZ_prom`); the stripe disjointness
`hD` is `freshLabel_inj` at the single width `c.n` (`hD_thread`, `hD_prom`).
-/
namespace TermFreshU
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermBal TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **Thread step, freshness** at a label the step does not allocate (the `j ≠ i` arm of `freshT_holds`). -/
theorem freshX_thread {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {x : AllocLabel} (hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc x) (old : FreshX Eg c x) :
    FreshX (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' x := by
  have hgf := gfoot_of X Y Z
  have hnO : ¬ Eg.OwnAt i x := fun ⟨cl, hc, _⟩ => by rw [old.1] at hc; cases hc
  refine ⟨?_, ?_, ?_, ?_, fun t m' hm' hl => ?_⟩
  · show (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto _ = none
    rcases hgf.2.1 x with e | ⟨hF, -⟩
    · rw [e]; exact old.1
    · exact absurd hF hnF
  · show (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').box _ = none
    rcases hgf.2.2.1 x with e | ⟨hF, -⟩
    · rw [e]; exact old.2.1
    · exact absurd hF hnF
  · show (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').ini _ = 0
    rcases (hgf.2.2.2.1 x).2 with e | hF | hO
    · rw [e]; exact old.2.2.1
    · exact absurd hF hnF
    · exact absurd hO hnO
  · show (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').pfr _ = none
    rcases hgf.2.2.2.2.1 x with e | ⟨-, -, -, -, hO⟩ | ⟨hF, -⟩
    · rw [e]; exact old.2.2.2.1
    · exact absurd hO hnO
    · exact absurd hF hnF
  · rcases Nat.lt_or_ge t c.mem.size with h1 | h1
    · rw [tctx_pre X t h1] at hm'; exact old.2.2.2.2 t m' hm' hl
    · rcases tctx_writeAt X t m' h1 hm' with hF | ⟨cl, hc⟩
      · rw [hl] at hF; exact hnF hF
      · rw [hl] at hc; have h0 := old.1; rw [cutSto_sub hc] at h0; cases h0

/-- **Thread step, own key** at a label the step does not allocate (`ownFresh_thread`, label-generic). -/
theorem ownZ_thread (hb1 : AllocGT p k arch Sp Init MintOK c0) (hN : PromNodupR p k arch Sp c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hK : ∀ t l, crS t (.own l) = cr i t (.own l))
    {x : AllocLabel} (hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc x) (h : OwnZ c Tot HP HS cr x) :
    OwnZ c' (upd Tot i Tot') (upd HP i HP') HS' (updD cr i cr' δ) x := by
  have hsz : c'.ths.size = c.ths.size := TermStep.threadSteps_size X.hc'
  have hi : i < c.ths.size := TermLiveProps.lt_of_get X.hth
  obtain ⟨hz, hzS⟩ := h
  have hF0 : F (.own x) = 0 := by
    cases e : F (.own x) with
    | zero => rfl
    | succ n => exact absurd (hb1 X Y (Z.toC _ _ _ _ _) x (by rw [e]; exact Nat.succ_ne_zero n)) hnF
  have hPC : TermPlant.PromCrK E' (stOf r.1 r.2.1 r.2.2) cr' db' := Z.2.2.2.2.2.1
  have hd0 : pSum (stOf r.1 r.2.1 r.2.2) db' (.own x) = 0 := (TermOwnFresh.promCrK_own hPC x).2
  have hzi := hz i hi
  obtain ⟨-, -, -, -, -, -, hsum⟩ := Y
  obtain ⟨-, -, -, -, -, -, -, -, -, -, Fd, hFd, hineq, -⟩ := Z
  have hI := hineq (.own x)
  have hT := congrFun hsum (.own x)
  rw [pSumAt_some X.hth (cr i)] at hzi
  simp only [Res.add_apply] at hI hT hzi
  rw [TermBal.pSum_congr_key (fun t => hK t x)] at hI
  refine ⟨fun n hn => ?_, by omega⟩
  rw [hsz] at hn
  by_cases hni : n = i
  · subst hni
    rw [upd_self, upd_self, updD_self, thread_pSumAt_self X]
    simp only [Res.add_apply]
    omega
  · have hzn := hz n hn
    have hδ := CrShift_sum hFd X.inv.disj (hN c X.run) (.own x) [n]
      (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩)
    rw [upd_other _ _ hni, upd_other _ _ hni, updD_other _ _ _ hni, thread_pSumAt_other X hni]
    simp only [Res.add_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hzn hδ ⊢
    rw [pSumAt_add]
    omega

/-- **Promise step, freshness** at a label outside the promiser's stripe (`freshP_holds`, label-generic). -/
theorem freshX_prom {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
    {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat} (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {x : AllocLabel} (hnP : ∀ m, x ≠ freshLabel c.lbase c.n j m) (old : FreshX Eg c x) :
    FreshX (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w) x := by
  refine ⟨old.1, old.2.1, ?_, ?_, fun t m' hm' hl => ?_⟩
  · show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).ini _ = 0
    simp only [plantG]
    split
    · rename_i f hf
      obtain ⟨-, ⟨cl, hc, -⟩, -⟩ := hspec X _ f hf
      rw [old.1] at hc; cases hc
    · exact old.2.2.1
  · show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr _ = none
    simp only [plantG]
    split
    · rename_i f hf
      obtain ⟨-, ⟨cl, hc, -⟩, -⟩ := hspec X _ f hf
      rw [old.1] at hc; cases hc
    · exact old.2.2.2.1
  · rw [prom_mem X.hth] at hm'
    rcases push_get hm' with ⟨-, h2⟩ | ⟨rfl, rfl⟩
    · exact old.2.2.2.2 t m' h2 hl
    · rcases (pctx_promLoc hpl X).2.2 with ⟨cl, hc⟩ | ⟨m0, -, e⟩
      · have hl' : a.label = x := hl
        rw [hl', old.1] at hc; cases hc
      · exact hnP m0 ((show a.label = x from hl).symm.trans e)

/-- **Promise step, own key** (`ownFresh_prom`, label-generic). -/
theorem ownZ_prom {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0)
    {x : AllocLabel} (h : OwnZ c Tot HP HS cr x) :
    OwnZ (promise c j a v w) Tot (upd HP j HP') HS' (upd cr j cr') x := by
  have hsz : (promise c j a v w).ths.size = c.ths.size := TermStep.promise_size c j a v w
  obtain ⟨hz, hzS⟩ := h
  have hj : j < c.ths.size := TermLiveProps.lt_of_get X.hth
  have hzj := hz j hj
  rw [pSumAt_some X.hth (cr j)] at hzj
  unfold PAcct at hA
  have hA' := congrFun hA (.own x)
  have hd := hdb x
  have hd0 : pSum (stOf c.mem c.pairs th) (db j) (.own x) = 0 := by
    obtain ⟨S0, -, -, -, -, -, hK⟩ := X.inv.thr j th X.hth
    exact (TermOwnFresh.promCrK_own hK x).2
  simp only [Res.add_apply] at hA' hzj
  refine ⟨fun n hn => ?_, by omega⟩
  rw [hsz] at hn
  by_cases hnj : n = j
  · subst hnj
    rw [upd_self, upd_self, promise_pSumAt_self X.hth]
    simp only [Res.add_apply]
    omega
  · rw [upd_other _ _ hnj, upd_other _ _ hnj, promise_pSumAt_other hnj]
    exact hz n hn

/-! ## `FreshU` wrappers -/

/-- **Thread step.** `hD`: the step allocates in no unborn stripe (M0: `freshLabel_inj` at width `c.n`,
`i < ths.size ≤ q`). Witnesses as in `ownFresh_thread` (pre-pool `updD`; see `ownZ_mono` for `cr2`). -/
theorem freshU_thread (hb1 : AllocGT p k arch Sp Init MintOK c0) (hN : PromNodupR p k arch Sp c0) {N : Nat}
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (ZC : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hK : ∀ t l, crS t (.own l) = cr i t (.own l))
    (hD : ∀ q j, c.ths.size ≤ q → q < N → ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc (freshLabel c.lbase N q j))
    (h : FreshU N Eg c Tot HP HS cr) :
    FreshU N (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' (upd Tot i Tot') (upd HP i HP') HS'
      (updD cr i cr' δ) := by
  have hsz : c'.ths.size = c.ths.size := TermStep.threadSteps_size X.hc'
  have hlb : c'.lbase = c.lbase := (threadSteps_lbase X.hc').1
  intro q j hq hqN
  rw [hsz] at hq; rw [hlb]
  obtain ⟨h1, h2⟩ := h q j hq hqN
  exact ⟨freshX_thread X Y ZC (hD q j hq hqN) h1, ownZ_thread hb1 hN X Y Z hK (hD q j hq hqN) h2⟩

/-- `OwnZ` is antitone in the credits (the pool re-split `cr2 ≤ updD cr …` keywise). -/
theorem ownZ_mono {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr cr2 : Nat → Ts → Res} {x : AllocLabel}
    (hle : ∀ n t, cr2 n t (.own x) ≤ cr n t (.own x)) (h : OwnZ c Tot HP HS cr x) : OwnZ c Tot HP HS cr2 x := by
  refine ⟨fun n hn => ?_, h.2⟩
  have h3 := h.1 n hn
  have h4 := TermPoolThread.pSumAt_key_le c n (f := cr2 n) (g := cr n) (key := .own x) (fun t => hle n t)
  simp only [Res.add_apply] at h3 ⊢
  omega

/-- **Promise step.** `hD`: no unborn label is in the promiser's stripe (M0: `freshLabel_inj`). -/
theorem freshU_prom {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
    {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
    (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0) {N : Nat}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0)
    (hD : ∀ q jj, c.ths.size ≤ q → q < N → ∀ m, freshLabel c.lbase N q jj ≠ freshLabel c.lbase c.n j m)
    (h : FreshU N Eg c Tot HP HS cr) :
    FreshU N (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w) Tot
      (upd HP j HP') HS' (upd cr j cr') := by
  have hsz : (promise c j a v w).ths.size = c.ths.size := TermStep.promise_size c j a v w
  have hlb : (promise c j a v w).lbase = c.lbase := by
    rw [(promise_inv (a := a) (v := v) (w := w) X.hth).1]
  intro q jj hq hqN
  rw [hsz] at hq; rw [hlb]
  obtain ⟨h1, h2⟩ := h q jj hq hqN
  exact ⟨freshX_prom (plantN := plantN) hspec hpl X (hD q jj hq hqN) h1, ownZ_prom X hA hdb h2⟩

/-- **No unborn stripe** (e.g. an InitOK start with `n = ths.size`): `FreshU` is vacuous. -/
theorem freshU_le {N : Nat} {Eg : GEnv} {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr : Nat → Ts → Res}
    (h : N ≤ c.ths.size) : FreshU N Eg c Tot HP HS cr :=
  fun _ _ hq hqN => absurd (Nat.lt_of_lt_of_le hqN h) (Nat.not_lt.2 hq)

end


/-- (M0) The stepping thread `i < ths.size` allocates in no unborn stripe at width `c.n`. -/
theorem hD_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i n n' : Nat}
    (hi : i < c.ths.size) :
    ∀ q j, c.ths.size ≤ q → q < c.n → ¬ FreshIn (gOf p k arch c i) n n' (freshLabel c.lbase c.n q j) := by
  rintro q j hq hqN ⟨m, -, -, e⟩
  have := (TermRun.freshLabel_inj hqN (Cfg.lt_n hi) e).1
  omega

/-- (M0) The promiser `j < ths.size`'s stripe misses every unborn stripe at width `c.n`. -/
theorem hD_prom {c : Cfg} {j : Nat} (hj : j < c.ths.size) :
    ∀ q jj, c.ths.size ≤ q → q < c.n → ∀ m, freshLabel c.lbase c.n q jj ≠ freshLabel c.lbase c.n j m := by
  intro q jj hq hqN m e
  have := (TermRun.freshLabel_inj hqN (Cfg.lt_n hj) e).1
  omega

/-- **InitShape start** (`initOK_of`'s witnesses: `Eg0 p`, all-zero totals/credits): `FreshU` at any width. -/
theorem freshU_init {p : Prog} {c0 : Cfg} (N : Nat) (hs : TermInit.InitShape p c0) :
    FreshU N (TermInit.Eg0 p) c0 (fun _ => .zero) (fun _ => .zero) .zero (fun _ _ => .zero) := by
  intro q j _ _
  refine ⟨⟨rfl, rfl, rfl, rfl, fun t m hm _ => ?_⟩, fun n _ => ?_, rfl⟩
  · rw [hs.mem] at hm; simp at hm
  · rw [TermInit.pSumAt_init (fun i th h => (hs.thr i th h).1)]; rfl

end TermFreshU

#print axioms TermFreshU.freshX_thread
#print axioms TermFreshU.ownZ_thread
#print axioms TermFreshU.freshX_prom
#print axioms TermFreshU.ownZ_prom
#print axioms TermFreshU.freshU_thread
#print axioms TermFreshU.freshU_prom
#print axioms TermFreshU.ownZ_mono
#print axioms TermFreshU.freshU_le
#print axioms TermFreshU.hD_thread
#print axioms TermFreshU.hD_prom
#print axioms TermFreshU.freshU_init
