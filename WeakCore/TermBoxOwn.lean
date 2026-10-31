import WeakCore.TermBNamed
import WeakCore.TermBoxZ

/-!
# TermBoxOwn: box payloads of a step name the stepper's cut (box L3, `payOwn`)

A typed reference to a box carries, in `VR`'s box clause, its payload typed (at
`η.unsee`), so the payload names labels `η` allocates (`vr_boxPay`).  Hence a
projection's payload names `Alloc η` with no global hypothesis on other boxes
(`projNV_useA`), every write of a typed thread step names the cut (`termWOK_cut`),
and a box the step creates names only labels of the stepper's cut.
-/

namespace TermBoxOwn
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermTyped TermCert TermBNamed
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem alloc_push0 (η : TEnv) (s : Ty) (l : AllocLabel) : Alloc (η.push0 s) l ↔ Alloc η l := by
  simp [Alloc, TEnv.push0, TEnv.ins, TEnv.insR]

theorem alloc_unsee (η : TEnv) (l : AllocLabel) : Alloc η.unsee l ↔ Alloc η l := by
  simp [Alloc, TEnv.unsee]

theorem allNV_of_labsV {Q : AllocLabel → Ts → Prop} {L : AllocLabel → Prop} (f : ∀ l v, Q l v → L l)
    {ws : List Word} (h : LabsV Q ws) : AllNV L ws :=
  fun w hw a g e => f _ _ (h w hw a g e)

/-- **A boxed value's box payload names allocated labels**: read at its own
shape (offset `s`), a reference to box `B` has `B.pay` naming only `Alloc η`. -/
theorem vr_boxPay : ∀ (t : Ty) (η : TEnv) (ρ : Nat → Nat) (s : Nat) (ws : List Word),
    sumSpine t → bh (shp t) → VR ρ η t (vsh s (shp t)) ws →
    ∀ (x : Address) (B : Box), ws.map (·.val) = [.loc x 0] → η.box x.label = some B → AllNV (Alloc η) B.pay
  | .refine t ψ, η, ρ, s, ws, hs, hb, h => vr_boxPay t η ρ s ws hs hb h.1
  | .mu b, η, ρ, s, ws, hs, hb, h => by
      intro x B hx hB
      have := vr_boxPay b _ ρ s ws hs hb h x B hx
        (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hB)
      exact AllNV.mono (fun l h => (alloc_push0 η _ l).1 h) this
  | .iall b, η, ρ, s, ws, hs, hb, h => vr_boxPay b η (vcons 0 ρ) s ws hs hb (h 0)
  | .iex b, η, ρ, s, ws, hs, hb, h => by
      simp only [VR, shp, vsh, Shp.iex.injEq] at h
      obtain ⟨n, rb, w, ⟨-, rfl⟩, h⟩ := h
      exact vr_boxPay b η _ s ws hs hb h
  | .tex κ b, η, ρ, s, ws, hs, hb, h => by
      simp only [VR, shp, vsh, Shp.tex.injEq] at h
      obtain ⟨n, rb, s', ⟨-, rfl⟩, -, -, h⟩ := h
      intro x B hx hB
      have := vr_boxPay b _ ρ s ws hs hb h x B hx
        (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hB)
      exact AllNV.mono (fun l h => (alloc_push0 η _ l).1 h) this
  | .sum a b, η, ρ, s, ws, _, hb, h => by
      intro x B hx hB
      have hS : (Ty.sum a b).tier = .boxed := by
        simp only [shp, bh] at hb; rw [← tier_lnorm]; exact hb
      simp only [VR, shp, vsh] at h
      obtain ⟨n, Ra, Rb, h1, h⟩ := h
      simp only [lnorm, Shp.sum.injEq, Ty.sum.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      rcases h with ⟨-, x', s', B', hx', -, hB', hn, -, -, hA, hBb⟩ | ⟨j, p, hd, -, -⟩
      · have e1 : x' = x := by
          rw [hx] at hx'; simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hx'
          exact hx'.symm
        subst e1
        rw [hB] at hB'; cases hB'
        simp only [Option.some.injEq, Nat.add_right_cancel_iff] at hn
        subst hn
        have la : (armsOf (lnorm a)).length = (armsOf a).length := by rw [armsOf_lnorm, List.length_map]
        by_cases hj : B.tag - s < (armsOf (lnorm a)).length
        · obtain ⟨hA1, hA2⟩ := hA hj
          cases hra : isBoxed a
          · obtain ⟨q, hq, hs2, hw2, hV2, hvq⟩ := hA2 (by rw [isBoxed_lnorm]; exact hra)
            rw [shp_lnorm] at hvq
            have hwc : wc a = some q.length := by
              obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hw2
              obtain ⟨us, hus, hnk⟩ := wc_some hk
              rw [← wc_lnorm, hk, hs2 us hus, hnk]
            have hl := ofArm_labsV hq (noJunkA a η.unsee ρ q hwc hV2 hvq)
            exact allNV_of_labsV (fun l _ h => (alloc_unsee η l).1 h) hl
          · have hv1 := hA1 (by rw [isBoxed_lnorm]; exact hra)
            rw [shp_lnorm] at hv1
            exact vr_boxPay a η ρ s ws (sumSpine_of_isBoxed a hra) (bh_shp a hra) hv1 _ B hx hB
        · have hj' : (armsOf (lnorm a)).length ≤ B.tag - s := Nat.le_of_not_lt hj
          obtain ⟨hB1, hB2⟩ := hBb hj'
          cases hrb : isBoxed b
          · obtain ⟨q, hq, hs2, hw2, hV2, hvq⟩ := hB2 (by rw [isBoxed_lnorm]; exact hrb)
            rw [shp_lnorm] at hvq
            have hwc : wc b = some q.length := by
              obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hw2
              obtain ⟨us, hus, hnk⟩ := wc_some hk
              rw [← wc_lnorm, hk, hs2 us hus, hnk]
            have hl := ofArm_labsV hq (noJunkA b η.unsee ρ q hwc hV2 hvq)
            exact allNV_of_labsV (fun l _ h => (alloc_unsee η l).1 h) hl
          · have hv1 := hB1 (by rw [isBoxed_lnorm]; exact hrb)
            rw [shp_lnorm] at hv1
            exact vr_boxPay b η ρ _ ws (sumSpine_of_isBoxed b hrb) (bh_shp b hrb) hv1 _ B hx hB
      · have htl : (Ty.sum (lnorm a) (lnorm b)).tier = .boxed := by
          rw [← hS]; exact tier_lnorm (.sum a b)
        rw [htl] at hd; simp [decodeArm] at hd
  | .intS _, _, _, _, _, hs, _, _ | .int, _, _, _, _, hs, _, _ | .fix _ _, _, _, _, _, hs, _, _
  | .lanes _ _, _, _, _, _, hs, _, _ | .prod _ _, _, _, _, _, hs, _, _ | .code _ _ _, _, _, _, _, hs, _, _
  | .tvar _, _, _, _, _, hs, _, _ | .ptr _ _, _, _, _, _, hs, _, _ | .ptrOpt _ _, _, _, _, _, hs, _, _
  | .loc _ _, _, _, _, _, hs, _, _ | .unit, _, _, _, _, hs, _, _ | .void, _, _, _, _, hs, _, _
  | .array _ _, _, _, _, _, hs, _, _ | .share _, _, _, _, _, hs, _, _ | .cap _ _, _, _, _, _, hs, _, _
  | .word _ _, _, _, _, _, hs, _, _ | .tok _ _, _, _, _, _, hs, _, _ | .word2 _ _, _, _, _, _, hs, _, _
  | .tok2 _ _ _ _, _, _, _, _, hs, _, _ | .epair _ _, _, _, _, _, hs, _, _ | .tokE _ _ _, _, _, _, _, hs, _, _ => by
      simp [sumSpine] at hs


/-- `vr_boxPay` for an operand read at its runtime type `rt` (closed by `VR_close`). -/
theorem vr_boxPayT {η : TEnv} (hc : Coh η) {ρ : Nat → Nat} {t rt : Ty} {ws : List Word}
    (hrb : isBoxed rt = true) (hsg : sig rt = sig (cl ρ η.wit 0 0 t)) (hv : VR ρ η t (shp rt) ws)
    (x : Address) (B : Box) (hx : ws.map (·.val) = [.loc x 0]) (hB : η.box x.label = some B) :
    AllNV (Alloc η) B.pay := by
  have hv0 : VR ρ η t (vsh 0 (shp rt)) ws := by rw [vsh_zero rt hrb]; exact hv
  have hvc : VR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 t) (vsh 0 (shp rt)) ws :=
    (VR_close hc ρ t [] 0 ρ (fun _ => 0) (vsh 0 (shp rt)) ws (fun _ => rfl)
      (fun _ hk => absurd hk (Nat.not_lt_zero _))).1 hv0
  rw [shp_of_sig hsg] at hvc
  have hsp : sumSpine (cl ρ η.wit 0 0 t) := by
    rw [← sumSpine_sig, ← hsg, sumSpine_sig]; exact sumSpine_of_isBoxed rt hrb
  have hbh : bh (shp (cl ρ η.wit 0 0 t)) := by rw [← shp_of_sig hsg]; exact bh_shp rt hrb
  exact vr_boxPay _ (CE η) _ 0 ws hsp hbh hvc x B hx hB

theorem projNV_useA {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c₁ : Cx} {env : Env} {s : St} {a : At} {t : Ty} {L : AllocLabel → Prop} (hE : EnvOK p η)
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx) (hbi : BoxInv g (CE η) s) (hu : cx.use a = .ok (t, c₁))
    (hL1 : ∀ l, Alloc η l → L l) : ProjNV L g env s a := by
  obtain ⟨-, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
  have hp := (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu).1
  have htb := (use_TvOK hu htv).2.1
  have hsig : sig rt = sig (cl ρ η.wit 0 0 t) :=
    lay_closed hi.2.2.2.1 hi.2.2.2.2.1 (peek_opaqueOK htv hp) htb hl
  have hws : AllNV L ws :=
    AllNV.mono hL1 (vr_named hE hi.2.2.2.1 hi.2.2.2.2.1 (peek_opaqueOK htv hp) htb hv hl)
  intro t' ws' he r hr hpa
  rw [hea] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  cases hrb : isBoxed rt
  · rw [projM_nbB hrb] at hr
    simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at hr
    obtain ⟨⟨j, q⟩, hq, rfl⟩ := hr
    exact asArm_nv hq hws
  · obtain ⟨w, x, B, arm, us, rfl, hw, hx0, hB, harm, hus, hnw, -, -, hsee⟩ :=
      boxed_operand hE.2.1 hbi hrb hsig hv
    obtain ⟨-, hpr⟩ := projM_own (g := g) (s := s) (t := rt) hbi hsee hrb hw hx0 hB harm hus hnw.symm
    obtain ⟨-, hWp, -⟩ := (hpr r hr).2 hpa
    exact allNV_wle hWp (AllNV.mono hL1 (vr_boxPayT hE.2.1 hrb hsig hv x B (by simp [hw]) hB))

/-- **A typed thread's writes name `L`** (`TermWOK`), for any `L` containing the labels `η`
allocates and the labels of `η`'s box payloads. -/
theorem termWOK_cut {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {L : AllocLabel → Prop}
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hL1 : ∀ l, Alloc η l → L l) :
    TermWOK L g (stOf mem pairs th) th := by
  have hbi : BoxInv g (CE η) (stOf mem pairs th) := hm.2.2.2.2.2.2.2.2.2.1
  have W1 : ∀ {a : At} {t : Ty} {c₁ : Cx}, cx.use a = .ok (t, c₁) → AtNV L th.env a :=
    fun hu => AtNV.mono hL1 (atNV_use hE hi htv hu)
  have W2 : ∀ {a : At} {j : Idx}, IntIdx cx a j → AtNV L th.env a :=
    fun hj => AtNV.mono hL1 (atNV_idx hE hi htv hj)
  have W3 : ∀ {b a : At} {t t' : Ty} {c₁ c₂ : Cx}, cx.use b = .ok (t, c₁) → c₁.use a = .ok (t', c₂) →
      AtNV L th.env a :=
    fun hb hu => AtNV.mono hL1 (atNV_use1 hE hi htv hb hu)
  have W4 : ∀ {b a : At} {t : Ty} {c₁ : Cx} {j : Idx}, cx.use b = .ok (t, c₁) → IntIdx c₁ a j →
      AtNV L th.env a :=
    fun hb hj => AtNV.mono hL1 (atNV_idx1 hE hi htv hb hj)
  have WP : ∀ {a : At} {t : Ty} {c₁ : Cx}, cx.use a = .ok (t, c₁) → ProjNV L g th.env (stOf mem pairs th) a :=
    fun hu => projNV_useA hE hi htv hbi hu hL1
  unfold TermWOK
  cases hterm : th.term with
  | let_ x op e =>
      rw [hterm] at hT
      cases hT with
      | let_ hop he =>
          cases hop
          all_goals (try simp only [OpWOK])
          all_goals first
            | trivial
            | exact WP (by assumption)
            | exact W1 (by assumption)
            | exact W2 (by assumption)
            | exact W3 (by assumption) (by assumption)
            | exact W4 (by assumption) (by assumption)
            | exact ⟨W2 (by assumption), W2 (by assumption)⟩
            | exact ⟨W4 (by assumption) (by assumption), W4 (by assumption) (by assumption)⟩
  | case a x e₁ y e₂ =>
      rw [hterm] at hT
      cases hT with
      | case hu _ _ _ _ => exact WP hu
  | cas acq rel w e v t ok fail =>
      rw [hterm] at hT
      cases hT
      all_goals first
        | exact W1 (by assumption)
        | exact W2 (by assumption)
  | casp acq rel w e0 e1 v0 v1 t ok fail =>
      rw [hterm] at hT
      cases hT
      all_goals exact ⟨W2 (by assumption), W2 (by assumption)⟩
  | _ => trivial


/-! ## The global step lemmas -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The labels whose unpublished cells are `i`'s. -/
def LOwn (Eg : GEnv) (i : Nat) (l : AllocLabel) : Prop :=
  ∀ cl, Eg.sto l = some cl → Eg.pfr l = none → cl.owner = some i

/-- **A box the step creates names only `LOwn`** (the stepper's cut, `termWOK_cut`; the box's
words are latest non-promise messages at its fresh label, written by the step). -/
theorem newBoxOwn_of :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
        (cr i) (db i) δ →
      TermBoxZ.BoxSto Eg →
      ∀ l B, FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l → E'.box l = some B →
        AllNV (LOwn Eg i) B.pay := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X _ Z hbs
  obtain ⟨S0, hRE0, -, hm0, -⟩ := X.inv.thr i th X.hth
  obtain ⟨ρ2, η2, cx2, Rf2, Rs2, hce0, hE2, hT2, htv2, hi2, -⟩ := hRE0
  have hce2 : CE η2 = Cut Eg i S0 := hce0
  have hm : MemInv (gOf p k arch c i) (CE η2) (stOf c.mem c.pairs th) := by rw [hce0]; exact hm0
  have hL1 : ∀ l, Alloc η2 l → LOwn Eg i l := by
    intro l h cl hcl hpf
    rcases h with ⟨c1, h⟩ | ⟨B, h⟩
    · have h' : (Cut Eg i S0).sto l = some c1 := by rw [← hce2]; exact h
      obtain ⟨e, ho⟩ := cutSto_some.1 h'
      rw [hcl] at e; cases e
      rcases ho with ho | ⟨f, hf⟩
      · exact ho
      · rw [hpf] at hf; cases hf
    · have h' : (Cut Eg i S0).box l = some B := by rw [← hce2]; exact h
      rw [hbs l B h'] at hcl; cases hcl
  have hw := termWOK_cut hT2.1 hi2.1 hE2 htv2 hm hL1
  have hpa : PromAbove (stOf r.1 r.2.1 r.2.2) := by
    have h1 := TermTyped.certified_promAboveSt X.cert X.e3
    rw [X.e1, X.e2] at h1
    exact h1
  have hwr := tstep_wrV X.hr hw hm.2.2.1 hpa
  intro l B hf hB' w hwB a g e
  have hbt := Z.2.2.1.2.2.2.2.2.2.2.2.2.1.2.1 l B hB'
  obtain ⟨o, ho⟩ := List.mem_iff_getElem?.1 hwB
  obtain ⟨t, -, ⟨m, hmt, hml, hmv, -⟩, hns, -⟩ := hbt.2 o w ho
  rcases hwr t m hmt hns with ⟨hold, hnp⟩ | hnv
  · obtain ⟨j, hj, -, el⟩ := hf
    have hpr := (X.inv.fresh i th X.hth j hj).2.2.2.2 t m hold (by rw [hml, el]; rfl)
    exact absurd hpr hnp
  · exact hnv a g (hmv.trans e)

/-- **`BoxSto` after a thread step**: a new box is at a fresh label, where `E'`'s
`BoxInv` empties the cell; an old box label keeps its (empty) cell. -/
theorem boxStoT_of :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
        (cr i) (db i) δ →
      TermBoxZ.BoxSto Eg → TermBoxZ.BoxSto (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hbs
  intro l B hB
  by_cases hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
  · have hB' : E'.box l = some B := by
      simp only [EgT, TermCut.GEnv.withFp, TermCut.GEnv.post, hf, ↓reduceIte] at hB
      exact hB
    have := (Z.2.2.1.2.2.2.2.2.2.2.2.2.1.2.2 l B hB').1
    simp only [EgT, TermCut.GEnv.withFp, TermCut.GEnv.post, hf, ↓reduceIte]
    exact this
  · have hB' : Eg.box l = some B := by
      simp only [EgT, TermCut.GEnv.withFp, TermCut.GEnv.post, hf, ↓reduceIte] at hB
      exact hB
    simp only [EgT, TermCut.GEnv.withFp, TermCut.GEnv.post, hf, ↓reduceIte]
    exact hbs l B hB'

/-- **`PayOwn` after a thread step**: an old box keeps its payload, which names `E_g`'s
labels (`SysInvN.bnamed`), none fresh, with cells, owners and unpublished frontiers as before;
a new box is `i`'s, and names `LOwn` labels (`newBoxOwn_of`). -/
theorem payOwnT_of :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
        (cr i) (db i) δ →
      TermBoxZ.BoxSto Eg → TermBoxZ.PayOwn Eg →
      TermBoxZ.PayOwn (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hbs hpo
  have G := TermInterf.gfoot_of X Y Z
  have hnf : ∀ l, GAlloc Eg l → ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := by
    rintro l hl ⟨j, hj, -, e⟩
    obtain ⟨h1, h2, -⟩ := X.inv.fresh i th X.hth j hj
    subst e
    rcases hl with ⟨c1, hc⟩ | ⟨B, hB⟩
    · have e := h1.symm.trans hc
      cases e
    · have e := h2.symm.trans hB
      cases e
  have hpf0 : ∀ a, (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr a = none → Eg.pfr a = none := by
    intro a h
    rcases G.2.2.2.2.1 a with e | ⟨h0, f, e, -⟩ | ⟨-, h0, -⟩
    · rw [← e]; exact h
    · exact h0
    · exact h0
  intro l B hB w hwB a g e cl hcl hpf
  have hpf' := hpf0 a.label hpf
  rcases G.2.2.1 l with eb | ⟨hf, -, B', hB', hown⟩
  · have hB0 : Eg.box l = some B := by rw [← eb]; exact hB
    have hna := hnf a.label (X.inv.bnamed l B hB0 w hwB a g e)
    have hcl0 : Eg.sto a.label = some cl := by
      rcases G.2.1 a.label with es | ⟨hfa, -⟩
      · rw [← es]; exact hcl
      · exact absurd hfa hna
    exact hpo l B hB0 w hwB a g e cl hcl0 hpf'
  · have e1 : B' = B := by
      have : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').box l = some B' := hB'
      rw [hB] at this; cases this; rfl
    subst e1
    rw [hown]
    have hBE : E'.box l = some B' := by
      simp only [EgT, TermCut.GEnv.withFp, TermCut.GEnv.post, hf, ↓reduceIte] at hB
      exact hB
    rcases G.2.1 a.label with es | ⟨-, -, -, T, eT⟩
    · have hcl0 : Eg.sto a.label = some cl := by rw [← es]; exact hcl
      exact newBoxOwn_of X Y Z hbs l B' hf hBE w hwB a g e cl hcl0 hpf'
    · have : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto a.label = some ⟨T, some (gOf p k arch c i).i⟩ := eT
      rw [hcl] at this; cases this; rfl

end


/-! ## Promise steps: `plantG` keeps cells and boxes and only adds frontiers -/

theorem plantG_pfr_none {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {l : AllocLabel}
    (h : (plantG Eg P N).pfr l = none) : Eg.pfr l = none := by
  simp only [plantG] at h
  split at h
  · cases h
  · exact h

theorem payOwn_egP {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}
    (h : TermBoxZ.PayOwn Eg) : TermBoxZ.PayOwn (EgP Eg P N j n) :=
  fun l B hB w hw a g e cl hcl hpf => h l B hB w hw a g e cl hcl (plantG_pfr_none (N := N) hpf)

theorem boxSto_egP {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}
    (h : TermBoxZ.BoxSto Eg) : TermBoxZ.BoxSto (EgP Eg P N j n) := h

theorem boxPV_egP {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}
    (h : TermBoxZ.BoxPV Eg) : TermBoxZ.BoxPV (EgP Eg P N j n) := h

theorem boxFrLe_egP {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j t n m : Nat}
    (h : TermBoxZ.BoxFrLe Eg n) (hm : n ≤ m) : TermBoxZ.BoxFrLe (EgP Eg P N j t) m :=
  fun l B hB => Nat.le_trans (h l B hB) hm


/-! ## Box frontiers (A1: a new box's frontier is the stepper's new `vWr`) -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- A box the step creates: `i`'s, with frontier at most the stepper's new `vWr`. -/
theorem newBox_fr :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
        (cr i) (db i) δ →
      ∀ l B, Eg.box l = none → E'.box l = some B → B.fr ≤ r.2.2.vs.vWr := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z l B hb0 hB
  have hc : (CE η).box l = Eg.box l := by rw [Y.1]; rfl
  rcases Z.1.2.2.2.1 l with e | ⟨-, B', hB', -, -, hfw, -⟩
  · rw [e, hc, hb0] at hB; cases hB
  · rw [hB] at hB'; cases hB'; exact hfw

theorem boxFrOwnT_of :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
        (cr i) (db i) δ →
      TermBoxZ.BoxFrOwn Eg c → TermBoxZ.BoxFrOwn (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hbo
  have G := TermInterf.gfoot_of X Y Z
  have hmono : th.vs.vWr ≤ r.2.2.vs.vWr := (TermTyped.tstep_wrUp _ _ _ _ r X.hr).1
  intro l B hB th' hth'
  rcases G.2.2.1 l with eb | ⟨hf, hb0, B', hB', hown⟩
  · have hB0 : Eg.box l = some B := by rw [← eb]; exact hB
    by_cases hi : B.own = i
    · rw [hi, X.e3] at hth'; cases hth'
      have h0 := hbo l B hB0 th (by rw [hi]; exact X.hth)
      exact Nat.le_trans h0 hmono
    · rw [X.ho _ hi] at hth'
      exact hbo l B hB0 th' hth'
  · have e1 : B' = B := by
      have : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').box l = some B' := hB'
      rw [hB] at this; cases this; rfl
    subst e1
    have hBE : E'.box l = some B' := by
      simp only [EgT, TermCut.GEnv.withFp, TermCut.GEnv.post, hf, ↓reduceIte] at hB
      exact hB
    have hi : B'.own = i := hown
    rw [hi, X.e3] at hth'; cases hth'
    exact newBox_fr X Y Z l B' hb0 hBE

theorem boxFrLeT_of :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
        (cr i) (db i) δ →
      TermBoxZ.BoxFrLe Eg c.mem.size →
      TermBoxZ.BoxFrLe (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c'.mem.size := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hbl
  have G := TermInterf.gfoot_of X Y Z
  have hsz : c.mem.size ≤ c'.mem.size := by
    rw [X.e1]; exact (TermLiveProps.tstep_ext _ _ _ _ r X.hr).mem.size
  have hv : r.2.2.vs.vWr ≤ c'.mem.size := by rw [X.e1]; exact TermStepper.tstep_vWr X.hr (X.inv.vwr i th X.hth)
  intro l B hB
  rcases G.2.2.1 l with eb | ⟨hf, hb0, B', hB', -⟩
  · have hB0 : Eg.box l = some B := by rw [← eb]; exact hB
    exact Nat.le_trans (hbl l B hB0) hsz
  · have hBE : E'.box l = some B := by
      simp only [EgT, TermCut.GEnv.withFp, TermCut.GEnv.post, hf, ↓reduceIte] at hB
      exact hB
    exact Nat.le_trans (newBox_fr X Y Z l B hb0 hBE) hv

/-- `BoxFrOwn` after a promise step: no `vWr` moves. -/
theorem boxFrOwn_promise {Eg Eg' : GEnv} {c : Cfg} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hb : ∀ l B, Eg'.box l = some B → Eg.box l = some B)
    (hj : c.ths[j]? = some th) (h : TermBoxZ.BoxFrOwn Eg c) : TermBoxZ.BoxFrOwn Eg' (promise c j a v w) := by
  intro l B hB thi hi
  rw [(promise_inv (a := a) (v := v) (w := w) hj).1] at hi
  by_cases hij : B.own = j
  · rw [hij, arr_get_set_eq _ hj] at hi; cases hi
    have := h l B (hb l B hB) th (by rw [hij]; exact hj)
    exact this
  · rw [arr_get_set_ne _ _ (Ne.symm hij)] at hi
    exact h l B (hb l B hB) thi hi

end

end TermBoxOwn

#print axioms TermBoxOwn.vr_boxPay
#print axioms TermBoxOwn.vr_boxPayT
#print axioms TermBoxOwn.projNV_useA
#print axioms TermBoxOwn.termWOK_cut
#print axioms TermBoxOwn.newBoxOwn_of
#print axioms TermBoxOwn.boxStoT_of
#print axioms TermBoxOwn.payOwnT_of
#print axioms TermBoxOwn.payOwn_egP
#print axioms TermBoxOwn.boxFrLe_egP
#print axioms TermBoxOwn.boxFrOwnT_of
#print axioms TermBoxOwn.boxFrLeT_of
#print axioms TermBoxOwn.boxFrOwn_promise
