import WeakCore.TermPtrRtsThr
import WeakCore.OwnFreshW5
import WeakCore.FootNCE
import WeakCore.TermFootBP0

/-!
# TermPtrRtsGLT: the staging package `PtrRtsGL` across a thread step

`ptrRtsGL_thread`: from `PtrRtsGL Eg Tot HP c` before a thread step of `i`, `PtrRtsGL` at
`EgT Eg (gOf ..) th.nalloc r.2.2.nalloc E' c'` with the updated frame totals and holdings.
K-2a (`PtrRtsThreadGL`) and `FootNCE` are explicit staging hypotheses.  Certificate facts: `PromAllocF`
(`hA`), used only through the single site `ownProm_sto_keep` (`OwnFreshW5`); `AllocGT` (`hb1`); and the
baseline `certified_promAboveSt` (`X.cert`, in `kApp`).

* owner `i`: a gated cell is old (a fresh cell has no frontier after the step), its frontier is old
  (a new one is the step's `publish`, `pfrNew_pub`, against the held key, `keyHeld_not_pub_C_contra`),
  its key was held before (`ownKey_noIncrease_thread_noHS`): K-2a applies at `sto = Eg.sto`.
* owner `j ≠ i`: `tminG`, frontier and key are unchanged; old messages keep their cells' types
  (`msgStoKeep`: a message below the old size at a fresh label is an outstanding promise of `i`,
  kept by `alloc_noFulfil`, so `ownProm_sto_keep` applies); new messages are above every promise.
* `LblSto` at `i` is K-2a's `ThLbl` conclusion, at a label no promise of `th` names and `th` does not
  publish (`exists_free`).
-/

namespace TermPtrRtsK

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermMain TermInterf TermPlantF TermPromClos TermCert TermGlob TermTyped TermPtrRts TermGranW TermBal
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- The hypotheses of `ptrRtsGL_thread`, bundled (internal). -/
structure GLT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 c c' : Cfg)
    (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) (i : Nat) (th : TTh)
    (r : Memory × List Ts × TTh) (S : AllocLabel → Prop) (ρ : Nat → Nat) (η : TEnv) (cx : Cx) (Rf Rs : Res)
    (E' : TEnv) (Tot' HP' HS' C F : Res) (cr' db' δ crS : Ts → Res) : Prop where
  hK : PtrRtsThreadGL p
  hk : k.storeDepRts = true
  hb1 : AllocGT p k arch Sp Init MintOK c0
  hA : PromAllocF p k arch Sp Init MintOK c0
  X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r
  Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs
  Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
    crS (db i) δ
  hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S
  hKS : ∀ t l, crS t (.own l) = cr i t (.own l)
  hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th)
  hPC : TermPtrKey.PubConsumeC th C
  hPfrP : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E'
  hNCE : FootNCE (CE η) E' r
  hG : PtrRtsGL Eg Tot HP c
  hGW : GranuleW Eg.sto c.mem c.pairs
  hLay : ∀ l cl, Eg.sto l = some cl → LayT cl.ty
  hsc : TermTyped.ScopeOK p th
  hdrf : TermScope.ThScope th
  hps : TermScope.ProgScopeOK p = true
  hPT : ProgT p
  hFBP : TermFootBP0.FootBP { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } E' th r
  hRP : RetPw th.σs th.stack cx.ret
  hBP : BoxPlantSep Eg Tot HP c

theorem egT_sto_fresh {Eg : GEnv} {g : G} {n n' : Nat} {E' : TEnv} {c' : Cfg} {l : AllocLabel}
    (h : FreshIn g n n' l) : (EgT Eg g n n' E' c').sto l = E'.sto l := post_sto_fresh h

/-! ## A label no promise names, not published -/

/-- The label a message names (0 if none). -/
def labOf : Option Msg → Nat
  | some m => match m.val with
    | .loc a _ => a.label
    | _ => 0
  | none => 0

theorem le_sum_mem {x : Nat} {L : List Nat} (h : x ∈ L) : x ≤ L.sum := by
  induction L with
  | nil => cases h
  | cons y L ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with e | h'
    · omega
    · have := ih h'; omega

theorem pubAt_uniq {th : TTh} {a1 a2 : AllocLabel} (h1 : TermOwnG0Defs.PubAt th a1)
    (h2 : TermOwnG0Defs.PubAt th a2) : a1 = a2 := by
  obtain ⟨y, x1, e, rt, ws, ad, ht, hev, hws, hl⟩ := h1
  obtain ⟨y', x2, e', rt', ws', ad', ht', hev', hws', hl'⟩ := h2
  rw [ht] at ht'
  cases ht'
  rw [hev] at hev'
  cases hev'
  rw [hws] at hws'
  cases hws'
  rw [← hl, ← hl']

theorem exists_free (th : TTh) (mem : Memory) : ∃ a, ¬ TermOwnG0Defs.PubAt th a ∧
    ∀ u ∈ th.promises, ∀ m, mem[u]? = some m → ∀ (a' : Address) (g : Nat), m.val = .loc a' g → a'.label ≠ a := by
  obtain ⟨N, hN⟩ : ∃ N, N = (th.promises.map fun u => labOf mem[u]?).sum := ⟨_, rfl⟩
  have hb : ∀ u ∈ th.promises, ∀ m, mem[u]? = some m → ∀ (a' : Address) (g : Nat), m.val = .loc a' g →
      a'.label ≤ N := by
    intro u hu m hm a' g hv
    have h1 : labOf mem[u]? = a'.label := by rw [hm]; simp only [labOf, hv]
    rw [hN, ← h1]
    exact le_sum_mem (List.mem_map.2 ⟨u, hu, rfl⟩)
  by_cases hp : TermOwnG0Defs.PubAt th (N + 1)
  · refine ⟨N + 2, fun h2 => ?_, fun u hu m hm a' g hv e => ?_⟩
    · have h3 : N + 1 = N + 2 := pubAt_uniq hp h2
      exact absurd (Nat.add_left_cancel h3) (by decide)
    · have h3 : a'.label ≤ N := hb u hu m hm a' g hv
      rw [e] at h3
      exact Nat.not_succ_le_self N (Nat.le_trans (Nat.le_succ _) h3)
  · refine ⟨N + 1, hp, fun u hu m hm a' g hv e => ?_⟩
    have h3 : a'.label ≤ N := hb u hu m hm a' g hv
    rw [e] at h3
    exact Nat.not_succ_le_self N h3

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
  {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
  {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ crS : Ts → Res}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-! ## Step facts -/

theorem gfreshL_of
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS)
    {l : AllocLabel} (hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l) : GFreshL Eg c th l := by
  obtain ⟨q, hq, -, hl⟩ := hf
  rw [hl]
  exact H.X.inv.fresh i th H.X.hth q hq

theorem ceFresh
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS)
    {l : AllocLabel} (hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l) :
    (CE η).sto l = none ∧ (CE η).box l = none ∧ (CE η).ini l = 0 ∧ (CE η).pfr l = none := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gfreshL_of H hf
  rw [H.Y.1]
  refine ⟨?_, h2, h3, h4⟩
  rw [Cut_sto]
  cases e : cutSto Eg i l with
  | none => rfl
  | some cl => rw [cutSto_sub e] at h1; cases h1

theorem footT
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS) :
    Foot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) :=
  ⟨H.Z.1.toP, fun _ hf => ceFresh H hf⟩

/-- A cell of `EgT` with a frontier is not at one of the step's fresh labels. -/
theorem notFresh
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS)
    {a : AllocLabel} {cl : Cell} {f : Ts}
    (hs : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto a = some cl)
    (hp : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr a = some f) :
    ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc a := by
  intro hf
  rw [egT_sto_fresh hf] at hs
  have hp' : E'.pfr a = some f := hp
  rcases H.Z.1.2.2.2.2.2.1 a with e | ⟨-, F0, -, -, -, hown, -⟩ | ⟨-, -, e⟩
  · rw [e, (ceFresh H hf).2.2.2] at hp'; cases hp'
  · obtain ⟨cc, hcc, -⟩ := hown
    rw [(ceFresh H hf).1] at hcc; cases hcc
  · rw [e] at hs; cases hs

theorem stoOld
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS)
    {a : AllocLabel} {cl : Cell} {f : Ts}
    (hs : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto a = some cl)
    (hp : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr a = some f) : Eg.sto a = some cl :=
  (TermPtrStab.EgT_sto_old (notFresh H hs hp)).symm.trans hs

theorem pfrKeepT
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS) :
    ∀ l f, Eg.pfr l = some f → (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = some f :=
  fun _ _ h => gfoot_pfr (gfoot_of H.X H.Y (H.Z.toC _ _ _ _ _)) h

theorem boxKeepT
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS) :
    ∀ l B, Eg.box l = some B → (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').box l = some B := by
  intro l B h
  by_cases hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
  · rw [(gfreshL_of H hf).2.1] at h; cases h
  · exact (post_box_old hf).trans h

/-- A message below the old size keeps its cell's type in `EgT` (at a fresh label it is an
outstanding promise of `i`, kept across an allocating step: `alloc_noFulfil`, then `ownProm_sto_keep`). -/
theorem msgStoKeep
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS)
    {u : Ts} {m : Msg} (hu : u < c.mem.size) (hm : c'.mem[u]? = some m) :
    (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto m.loc.label = Eg.sto m.loc.label := by
  by_cases hF : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label
  · have hm0 : c.mem[u]? = some m := (tctx_pre H.X u hu).symm.trans hm
    have hin := (gfreshL_of H hF).2.2.2.2 u m hm0 rfl
    obtain ⟨q, hq1, hq2, -⟩ := hF
    have hin' := TermPtrRtsThr.alloc_noFulfil H.X.hr (Nat.lt_of_le_of_lt hq1 hq2) u hin hu
    exact ownProm_sto_keep H.hA H.X H.Y (H.Z.toC _ _ _ _ _) H.hS H.hPfrP hin' hm
  · exact TermPtrStab.EgT_sto_old hF

theorem pfrOldFgn
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS)
    {a : AllocLabel} {cl : Cell} {f : Ts} {j : Nat}
    (hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc a) (hs0 : Eg.sto a = some cl)
    (ho : cl.owner = some j) (hji : j ≠ i)
    (hp : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr a = some f) : Eg.pfr a = some f := by
  rcases (gfoot_of H.X H.Y (H.Z.toC _ _ _ _ _)).2.2.2.2.1 a with e | ⟨-, f', -, -, ⟨cc, hcc, hoc⟩⟩ | ⟨hf, -, -⟩
  · rw [← e]; exact hp
  · rw [hs0] at hcc; cases hcc
    exact absurd (Option.some.inj (ho.symm.trans hoc)) hji
  · exact absurd hf hnf

theorem pfrOldOwn
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS)
    {a : AllocLabel} {cl : Cell} {f : Ts}
    (hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc a) (hs0 : Eg.sto a = some cl)
    (hp : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr a = some f)
    (hheld : 0 < (Tot' + HP') (.own a)) : ∃ f0, Eg.pfr a = some f0 := by
  cases e : Eg.pfr a with
  | some f0 => exact ⟨f0, rfl⟩
  | none =>
    exfalso
    have hpub := pfrNew_pub (gfoot_of H.X H.Y (H.Z.toC _ _ _ _ _)) (fun _ => rfl)
      (fun l h1 h2 => H.hPfrP l (by rw [H.Y.1]; exact h1) (by rw [H.Y.1]; exact h2)) hs0 e
      (fun h => by
        have h2 : E'.pfr a = none := h
        have h3 : E'.pfr a = some f := hp
        rw [h2] at h3; cases h3)
    exact TermPtrKey.keyHeld_not_pub_C_contra H.hb1 H.X H.Y H.Z H.hKS H.hPC hnf hheld hpub

/-! ## K-2a at the stepper -/

/-- K-2a (`PtrRtsThreadGL`) at `sto = Eg.sto`, `sto' = EgT.sto`, for a label `a` meeting its
per-label hypotheses. -/
theorem kApp
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS)
    (a : AllocLabel) (hP : PtrRtsE Eg.sto (stOf c.mem c.pairs th) th a) (hnp : ¬ TermOwnG0Defs.PubAt th a)
    (hC : ∀ t, tminOf Eg.sto (stOf c.mem c.pairs th) a = some t → MemRtsC Eg.sto t a c.mem c.pairs th.promises)
    (hfa : ∀ l, FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l → l ≠ a) (hBN : Eg.box a = none)
    (hBS : ∀ t, tminOf Eg.sto (stOf c.mem c.pairs th) a = some t → BoxSep (CE η) t a c.mem) :
    (PtrRtsE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto (stOf r.1 r.2.1 r.2.2) r.2.2 a ∧
      ∀ t, tminOf Eg.sto (stOf c.mem c.pairs th) a = some t →
        tminOf (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto (stOf r.1 r.2.1 r.2.2) a = some t) ∧
      ThLbl (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') r.2.2 ∧
      (∀ t, tminOf (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto (stOf r.1 r.2.1 r.2.2) a = some t →
        MemRtsC (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto t a r.1 r.2.1 r.2.2.promises) ∧
      GranuleWP (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto r.1 r.2.1 r.2.2.promises := by
  have h4 : ∀ l cl, (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl → Eg.sto l = none →
      (CE η).sto l = none ∧ E'.sto l = some cl := by
    intro l cl h hS
    by_cases hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
    · exact ⟨(ceFresh H hf).1, (egT_sto_fresh hf).symm.trans h⟩
    · rw [TermPtrStab.EgT_sto_old hf] at h; rw [h] at hS; cases hS
  have hpa : PromAbove (stOf r.1 r.2.1 r.2.2) := by
    have h1 := TermTyped.certified_promAboveSt H.X.cert H.X.e3
    rw [H.X.e1, H.X.e2] at h1
    exact h1
  have hRE : ThInvRE p (CE η) th (Tot i) :=
    ⟨ρ, η, cx, Rf, Rs, rfl, H.Y.2.2.1, H.Y.2.2.2.1, H.Y.2.2.2.2.1, H.Y.2.2.2.2.2.1, H.Y.2.2.2.2.2.2, H.hRP⟩
  exact H.hK (gOf p k arch c i) (CE η) E' Eg (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') Eg.sto
    (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto c.mem c.pairs th a r H.hk
    (fun l cl h => by rw [H.Y.1] at h; exact cut_sto_le Eg i S l cl h)
    (fun l cl h => by
      by_cases hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
      · exact (egT_sto_fresh hf).trans h
      · rw [TermPtrStab.EgT_sto_old hf]
        rcases H.Z.1.2.2.1 l with e | ⟨hf', -⟩
        · rw [e, H.Y.1] at h; exact cut_sto_le Eg i S l cl h
        · exact absurd hf' hf)
    (fun l cl h => by
      by_cases hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
      · rw [(gfreshL_of H hf).1] at h; cases h
      · rw [TermPtrStab.EgT_sto_old hf]; exact h)
    h4
    (fun l f h h' => by rw [H.Y.1, Cut_pfr, h'] at h; cases h)
    (fun l B h h' => by rw [H.Y.1, Cut_box, h'] at h; cases h)
    (fun l f h h' => by
      have h2 : E'.pfr l = none := h'
      rw [h] at h2; cases h2)
    (fun l B h h' => by
      by_cases hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
      · have h2 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').box l = none := h'
        rw [post_box_fresh hf, h] at h2; cases h2
      · have h2 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').box l = none := h'
        rw [post_box_old hf] at h2
        rcases H.Z.1.2.2.2.1 l with e | ⟨hf', -⟩
        · rw [e, H.Y.1, Cut_box, h2] at h; cases h
        · exact hf hf')
    (pfrKeepT H) (boxKeepT H) hRE.thInvE H.hm hP hnp H.X.hr (footT H) H.Z.2.1.thInvE hpa
    (fun u hu m hmu hS => by
      rw [ownProm_sto_keep H.hA H.X H.Y (H.Z.toC _ _ _ _ _) H.hS H.hPfrP hu (by rw [H.X.e1]; exact hmu)]; exact hS)
    (H.hG.2.1 i th H.X.hth) H.hsc H.hdrf H.hps hC (granuleWP_of _ H.hGW)
    (fun l hf => (gfreshL_of H hf).1) H.hLay
    (fun q hq m0 cl h0 hc hS => H.hNCE.1 q hq m0 cl h0 (h4 _ _ hc hS).2 (h4 _ _ hc hS).1)
    (fun v mv cl o hv hP hc hS ho hT => H.hNCE.2 v mv cl o hv hP (h4 _ _ hc hS).2 (h4 _ _ hc hS).1 ho hT)
    rfl H.hPT hfa (by rw [H.Y.1, Cut_box]; exact hBN) H.hFBP.1 H.hFBP.2 (fun _ _ => ⟨ρ, η, cx, rfl, H.Y.2.2.1, H.Y.2.2.2.1.1, H.Y.2.2.2.2.1, FInvR_FInv H.Y.2.2.2.2.1.2.2.2.2.2.2.2 (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs E rd ws R h) H.Y.2.2.2.2.2.1, H.hRP⟩)
    hBS

/-- K-2a at a gated cell of the stepper, and its old `tmin`. -/
theorem ownGate
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS)
    {a : AllocLabel} {cl : Cell} {f : Ts}
    (hs : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto a = some cl) (ho : cl.owner = some i)
    (hp : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr a = some f)
    (hk' : 0 < (upd Tot i Tot' i + upd HP i HP' i) (.own a)) :
    ((PtrRtsE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto (stOf r.1 r.2.1 r.2.2) r.2.2 a ∧
      ∀ t, tminOf Eg.sto (stOf c.mem c.pairs th) a = some t →
        tminOf (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto (stOf r.1 r.2.1 r.2.2) a = some t) ∧
      ThLbl (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') r.2.2 ∧
      (∀ t, tminOf (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto (stOf r.1 r.2.1 r.2.2) a = some t →
        MemRtsC (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto t a r.1 r.2.1 r.2.2.promises) ∧
      GranuleWP (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto r.1 r.2.1 r.2.2.promises) ∧
      ∃ t0, tminOf Eg.sto (stOf c.mem c.pairs th) a = some t0 := by
  have hnf := notFresh H hs hp
  have hs0 := stoOld H hs hp
  rw [upd_self, upd_self] at hk'
  have hk0 := Nat.lt_of_lt_of_le hk' (TermPtrKey.ownKey_noIncrease_thread_noHS H.hb1 H.X H.Y H.Z H.hKS hnf)
  obtain ⟨f0, hf0⟩ := pfrOldOwn H hnf hs0 hp hk'
  have hP := ptrRtsE_of_G H.hG.1 H.X.hth hs0 ho hf0 hk0
  have hC : ∀ t, tminOf Eg.sto (stOf c.mem c.pairs th) a = some t →
      MemRtsC Eg.sto t a c.mem c.pairs th.promises := fun t ht =>
    H.hG.2.2.2 i th a cl f0 H.X.hth hs0 ho hf0 hk0 t (by rw [tminG_eq H.X.hth]; exact ht)
  obtain ⟨t0, ht0⟩ := Option.ne_none_iff_exists'.1 (H.hG.2.2.1 i a cl f0 hs0 ho hf0 hk0)
  have hfa : ∀ l, FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l → l ≠ a := fun l hl he => by
    rw [he] at hl; rw [(gfreshL_of H hl).1] at hs0; cases hs0
  have hBS : ∀ t, tminOf Eg.sto (stOf c.mem c.pairs th) a = some t → BoxSep (CE η) t a c.mem := by
    intro t ht l B hB o w hw hN f hf
    rw [H.Y.1, Cut_box] at hB
    rw [H.Y.1, Cut_pfr] at hf
    exact H.hBP l B hB o w hw i th a cl f t H.X.hth hs0 ho hf hk0 (by rw [tminG_eq H.X.hth]; exact ht) hN
  refine ⟨kApp H a hP (TermPtrKey.keyHeld_not_pub_C_contra H.hb1 H.X H.Y H.Z H.hKS H.hPC hnf hk') hC hfa
    (TermPtrStab.box_none_of_sto H.X.inv.boxSto hs0) hBS, t0, ?_⟩
  rw [← tminG_eq H.X.hth]; exact ht0

/-! ## The four clauses -/

theorem ptrRtsG_T
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS) :
    PtrRtsG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (upd Tot i Tot') (upd HP i HP') c' := by
  intro j thj a cl f hj hs ho hp hk' t ht
  by_cases hji : j = i
  · rw [hji] at hj ho hk' ht
    rw [H.X.e3] at hj
    cases hj
    obtain ⟨⟨⟨hR, -⟩, -⟩, -⟩ := ownGate H hs ho hp hk'
    rw [tminG_eq H.X.e3, H.X.e1, H.X.e2] at ht
    rw [H.X.e1]
    exact hR t ht
  · have hs0 := stoOld H hs hp
    have hq : c.ths[j]? = some thj := (H.X.ho j hji).symm.trans hj
    rw [upd_other _ _ hji, upd_other _ _ hji] at hk'
    have hf0 := pfrOldFgn H (notFresh H hs hp) hs0 ho hji hp
    rw [TermPtrStab.tminG_thread_fgn H.X E' hji] at ht
    obtain ⟨hM, hR⟩ := H.hG.1 j thj a cl f hq hs0 ho hf0 hk' t ht
    refine ⟨fun u m hu hE hnp => ?_, hR⟩
    rw [tminG_eq hq] at ht
    have htl : t < c.mem.size := H.X.inv.plt j thj t hq (tminOf_spec ht).1
    rcases Nat.lt_or_ge u c.mem.size with hlt | hge
    · have hm0 : c.mem[u]? = some m := (tctx_pre H.X u hlt).symm.trans hu
      obtain ⟨⟨ca, hca, h1, h2⟩, h3⟩ := hE
      rw [msgStoKeep H hlt hu] at hca
      exact hM u m hm0 ⟨⟨ca, hca, h1, h2⟩, h3⟩ hnp
    · exact Nat.le_of_lt (Nat.lt_of_lt_of_le htl hge)

/-- A label no promise of `th` names, `th` does not publish, not fresh in the step, and no box. -/
theorem exists_freeT
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS) :
    ∃ a, ¬ TermOwnG0Defs.PubAt th a ∧
      (∀ u ∈ th.promises, ∀ m, c.mem[u]? = some m → ∀ (a' : Address) (g : Nat), m.val = .loc a' g → a'.label ≠ a) ∧
      (∀ l, FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l → l ≠ a) ∧ Eg.box a = none := by
  obtain ⟨N, hN⟩ : ∃ N, N = (th.promises.map fun u => labOf c.mem[u]?).sum := ⟨_, rfl⟩
  have hb : ∀ u ∈ th.promises, ∀ m, c.mem[u]? = some m → ∀ (a' : Address) (g : Nat), m.val = .loc a' g →
      a'.label ≤ N := by
    intro u hu m hm a' g hv
    have h1 : labOf c.mem[u]? = a'.label := by rw [hm]; simp only [labOf, hv]
    rw [hN, ← h1]
    exact le_sum_mem (List.mem_map.2 ⟨u, hu, rfl⟩)
  have hi : i < c.ths.size := lt_of_getq H.X.hth
  have hn : 0 < c.n := Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n hi)
  have hcand : ∀ q, N + th.nalloc + r.2.2.nalloc < q →
      (∀ u ∈ th.promises, ∀ m, c.mem[u]? = some m → ∀ (a' : Address) (g : Nat), m.val = .loc a' g →
        a'.label ≠ freshLabel c.lbase c.n i q) ∧
      (∀ l, FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l → l ≠ freshLabel c.lbase c.n i q) ∧
      Eg.box (freshLabel c.lbase c.n i q) = none := by
    intro q hq
    have hge : q ≤ freshLabel c.lbase c.n i q := by
      unfold freshLabel
      have : q ≤ c.n * q := Nat.le_mul_of_pos_left q hn
      omega
    refine ⟨fun u hu m hm a' g hv e => ?_, fun l ⟨j, hj1, hj2, hl⟩ e => ?_,
      (H.X.inv.fresh i th H.X.hth q (by omega)).2.1⟩
    · have h5 : freshLabel c.lbase c.n i q ≤ N := e ▸ hb u hu m hm a' g hv
      have h6 := Nat.le_trans hge h5
      omega
    · rw [hl] at e
      have := (TermRun.freshLabel_inj (Cfg.lt_n hi) (Cfg.lt_n hi) e).2
      omega
  obtain ⟨h1a, h1b, h1c⟩ := hcand (N + th.nalloc + r.2.2.nalloc + 1) (by omega)
  obtain ⟨h2a, h2b, h2c⟩ := hcand (N + th.nalloc + r.2.2.nalloc + 2) (by omega)
  by_cases hp : TermOwnG0Defs.PubAt th (freshLabel c.lbase c.n i (N + th.nalloc + r.2.2.nalloc + 1))
  · refine ⟨_, fun h2 => ?_, h2a, h2b, h2c⟩
    have e := (TermRun.freshLabel_inj (Cfg.lt_n hi) (Cfg.lt_n hi) (pubAt_uniq hp h2)).2
    omega
  · exact ⟨_, hp, h1a, h1b, h1c⟩

theorem lblSto_T
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS) :
    LblSto (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' := by
  obtain ⟨a, hna, hfree, hfa, hBN⟩ := exists_freeT H
  have hnone : tminOf Eg.sto (stOf c.mem c.pairs th) a = none := by
    cases h : tminOf Eg.sto (stOf c.mem c.pairs th) a with
    | none => rfl
    | some t =>
      obtain ⟨ht, m, hm, -, a', g, hv, hl⟩ := tminOf_spec h
      exact absurd hl (hfree t ht m hm a' g hv)
  have hR := kApp H a (fun t ht => by rw [hnone] at ht; cases ht) hna (fun t ht => by rw [hnone] at ht; cases ht)
    hfa hBN (fun t ht => by rw [hnone] at ht; cases ht)
  intro j thj hj
  by_cases hji : j = i
  · rw [hji, H.X.e3] at hj
    cases hj
    exact hR.2.1
  · rw [H.X.ho j hji] at hj
    obtain ⟨he, hst⟩ := H.hG.2.1 j thj hj
    exact ⟨envLbl_mono (pfrKeepT H) (boxKeepT H) he,
      fun f hf => envLbl_mono (pfrKeepT H) (boxKeepT H) (hst f hf)⟩

theorem gateTmin_T
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS) :
    GateTmin (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (upd Tot i Tot') (upd HP i HP') c' := by
  intro j a cl f hs ho hp hk'
  by_cases hji : j = i
  · rw [hji] at ho hk' ⊢
    obtain ⟨⟨⟨-, htm⟩, -⟩, t0, ht0⟩ := ownGate H hs ho hp hk'
    rw [tminG_eq H.X.e3, H.X.e1, H.X.e2, htm t0 ht0]
    exact fun h => by cases h
  · have hs0 := stoOld H hs hp
    rw [upd_other _ _ hji, upd_other _ _ hji] at hk'
    rw [TermPtrStab.tminG_thread_fgn H.X E' hji]
    exact H.hG.2.2.1 j a cl f hs0 ho (pfrOldFgn H (notFresh H hs hp) hs0 ho hji hp) hk'

theorem memRtsCG_T
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS) :
    MemRtsCG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (upd Tot i Tot') (upd HP i HP') c' := by
  intro j thj a cl f hj hs ho hp hk' t ht
  by_cases hji : j = i
  · rw [hji] at hj ho hk' ht
    rw [H.X.e3] at hj
    cases hj
    obtain ⟨⟨-, -, hC', -⟩, -⟩ := ownGate H hs ho hp hk'
    rw [tminG_eq H.X.e3, H.X.e1, H.X.e2] at ht
    rw [H.X.e1, H.X.e2]
    exact hC' t ht
  · have hs0 := stoOld H hs hp
    have hq : c.ths[j]? = some thj := (H.X.ho j hji).symm.trans hj
    rw [upd_other _ _ hji, upd_other _ _ hji] at hk'
    have hf0 := pfrOldFgn H (notFresh H hs hp) hs0 ho hji hp
    rw [TermPtrStab.tminG_thread_fgn H.X E' hji] at ht
    have hM := H.hG.2.2.2 j thj a cl f hq hs0 ho hf0 hk' t ht
    rw [tminG_eq hq] at ht
    have htl : t < c.mem.size := H.X.inv.plt j thj t hq (tminOf_spec ht).1
    intro u m cl' hu hnp hcl hN hor
    rcases Nat.lt_or_ge u c.mem.size with hlt | hge
    · have hm0 : c.mem[u]? = some m := (tctx_pre H.X u hlt).symm.trans hu
      rw [msgStoKeep H hlt hu] at hcl
      refine hM u m cl' hm0 hnp hcl hN ?_
      rcases hor with h | ⟨v, m0, hv, hvp, hvm, hl, hcp⟩
      · exact .inl h
      · right
        have hvlt : v < c.mem.size := by
          rw [← hv] at hlt
          exact Nat.lt_of_succ_lt hlt
        refine ⟨v, m0, hv, ?_, (tctx_pre H.X v hvlt).symm.trans hvm, hl, hcp⟩
        rcases tctx_pairs H.X v hvp with h | h
        · exact h
        · exact absurd (Nat.lt_of_le_of_lt h hvlt) (Nat.lt_irrefl _)
    · exact Nat.le_of_lt (Nat.lt_of_lt_of_le htl hge)

/-- **`ptrRtsGL_thread`**: the staging package `PtrRtsGL` across a thread step of `i`, at
`EgT` with `upd Tot i Tot'`, `upd HP i HP'` (`sysInv_thread`'s witnesses).  Staging (never at the
gate): `hRL` (sig form, until RetPw lands; then `PwEq`) and K-2a (`hK : PtrRtsThreadGL p`, closed by
`ptrRtsThreadGL_v3d` once `FulCntR` is discharged).  `hNCE`/`hFBP` come from `zfNB`.  `hm` (`MemInv` at the repicked
`CE η`), `hPC` (`PubConsumeC`, the consume export) and `hPfrP` (`hFp.pfrG`) are `sysInv_thread`'s;
`hGW` (`GranuleW`), `hLay` (`stoLay`) the SysInvN clauses; `hsc`/`hdrf`/`hps` the scope facts.
Certificate facts: `hA` (`PromAllocF`) through the single site `ownProm_sto_keep` only; `hb1` (`AllocGT`). -/
theorem ptrRtsGL_thread (hK : PtrRtsThreadGL p) (hk : k.storeDepRts = true)
    (hb1 : AllocGT p k arch Sp Init MintOK c0) (hA : PromAllocF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S) (hKS : ∀ t l, crS t (.own l) = cr i t (.own l))
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hPC : TermPtrKey.PubConsumeC th C)
    (hPfrP : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    (hNCE : FootNCE (CE η) E' r) (hG : PtrRtsGL Eg Tot HP c) (hGW : GranuleW Eg.sto c.mem c.pairs)
    (hLay : ∀ l cl, Eg.sto l = some cl → LayT cl.ty) (hsc : TermTyped.ScopeOK p th)
    (hdrf : TermScope.ThScope th) (hps : TermScope.ProgScopeOK p = true) (hPT : ProgT p)
    (hFBP : TermFootBP0.FootBP { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } E' th r)
    (hRP : RetPw th.σs th.stack cx.ret) (hBP : BoxPlantSep Eg Tot HP c) :
    PtrRtsGL (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (upd Tot i Tot') (upd HP i HP') c' :=
  have H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS :=
    ⟨hK, hk, hb1, hA, X, Y, Z, hS, hKS, hm, hPC, hPfrP, hNCE, hG, hGW, hLay, hsc, hdrf, hps, hPT, hFBP, hRP, hBP⟩
  ⟨ptrRtsG_T H, lblSto_T H, gateTmin_T H, memRtsCG_T H⟩

end

end TermPtrRtsK

#print axioms TermPtrRtsK.ptrRtsGL_thread
#print axioms TermPtrRtsK.msgStoKeep
#print axioms TermPtrRtsK.exists_free
