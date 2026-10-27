import WeakCore.TermNoHold
import WeakCore.TermIni
import WeakCore.TermXFO

/-!
# TermPlantF: plant and promise-typing fields

Step 1: `noBoxProm` (T17), via `certified_promLoc` started at the stepper's
post-step typing (`TOut`, `ThInvRE.thInvE`).
-/

namespace TermPlantF

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The run premise at a thread step, from the successor: scope and
`NoHoldPub` along every certificate of the stepper from `c'`, and the scope at `c` itself (the
post-step start, `TermXFO.anchPost`). -/
def CertRunT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
    ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    ScopeAt p i c ∧
      ∀ c1, Solo p k arch i c' c1 → Certified p k arch c1 i → ScopeAt p i c1 ∧ NoHoldPubA p k arch (Cut Eg i S) (Cut Eg i S) i c1

/-- **T17 `noBoxProm`**: after a step that creates a box at a fresh label, the
stepper has no outstanding promise there.  `certified_promLoc` from `c'`
(start environment `E'`): the promise lies at a cell of `E'` (but a box label
is no Σ cell, `BoxInv`) or at a label of index at least the new allocation
count (but the box label's index is below it). -/
theorem noBoxProm_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunT p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    NoBoxPromF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hS hPfr l B hfr hB t ht m hm
  have hAP := TermXFO.anchPost (hV0 := hV0) X Y.1 Z hS hPfr (hrun X S hS).1
  obtain ⟨hF, hRE, hm', -⟩ := Z
  have hg : gOf p k arch c' i = gOf p k arch c i := TermTyped.gOf_thread X.hc'
  have hSC0 : StoClo (CE η) := by
    rw [Y.1]; exact fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have hbo : (gOf p k arch c' i).boxFence = true := by rw [hg]; exact X.inv.bf
  have hst : stOf c'.mem c'.pairs r.2.2 = stOf r.1 r.2.1 r.2.2 := by rw [X.e1, X.e2]
  have h0 := InvAtXF_ofA (p := p) (k := k) (arch := arch) (Ea := Cut Eg i S) X.e3 hRE.thInvE (by rw [hg, hst]; exact hm')
    (StoClo_EFoot hF hSC0) hbo (by rw [hst]; exact hAP.1) (.inr hAP.2)
  have hloc := certified_promLoc (hPS := hPS) (hSub := hSub) (hSig := hSig) hP (fun c1 h1 h2 => ((hrun X S hS).2 c1 h1 h2).1) (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') (fun c1 h1 h2 => ((hrun X S hS).2 c1 h1 h2).2)
    h0 (TermTyped.tidAt_mono hAP.2 (TermTyped.tidAt_thread X.hc' (TermMain.tidAt_cut X.inv i S))) X.cert (by rw [TermFul.promsOf_some X.e3]; exact ht) hm
  intro hl
  rw [hl] at hloc
  rcases hloc with ⟨cl, hcl⟩ | ⟨jj, hjj, hlj⟩
  · have hbi := hm'.2.2.2.2.2.2.2.2.2.1
    rw [(hbi.2.2 l B hB).1] at hcl
    cases hcl
  · obtain ⟨j0, -, hj0, hl0⟩ := hfr
    have hi : i < c.ths.size := TermCert.arr_lt X.hth
    have hsz : c'.ths.size = c.ths.size := TermStep.threadSteps_size X.hc'
    have hlb : c'.lbase = c.lbase := (threadSteps_lbase X.hc').1
    rw [TermStep.threadSteps_n X.hc', hlb] at hlj
    have e := freshLabel_inj (base := c.lbase) (Cfg.lt_n hi) (Cfg.lt_n hi) (hlj.symm.trans hl0)
    omega

end

#print axioms noBoxProm_of

/-! ## `promNoTwoP`: a promise lies in no two-word unit -/

theorem list_split_at : ∀ (L : List Acc) (i : Nat) (x : Acc), L[i]? = some x → L = L.take i ++ x :: L.drop (i + 1)
  | [], _, _, h => by simp at h
  | y :: L, 0, x, h => by simp at h; simp [h]
  | y :: L, i + 1, x, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    exact congrArg (y :: ·) (list_split_at L i x h)

theorem oneAtF_append : ∀ {us : List Acc} {j : Nat} (post : List Acc), TermFul.OneAt us j →
    TermFul.OneAt (us ++ post) j
  | _, _, post, .here us => .here (us ++ post)
  | _, _, post, .cons u h => .cons u (oneAtF_append post h)

theorem oneAtF_prepend : ∀ (pre : List Acc) {us : List Acc} {j : Nat}, TermFul.OneAt us j →
    TermFul.OneAt (pre ++ us) (nWords pre + j)
  | [], _, j, h => by simpa [nWords] using h
  | u :: pre, us, j, h => by
    have h' := TermFul.OneAt.cons u (oneAtF_prepend pre h)
    have e : nWords pre + j + u.size = nWords (u :: pre) + j := by
      simp only [nWords, List.map_cons, List.sum_cons]; omega
    rw [e] at h'; exact h'

/-- Inside one laid-out segment: a `.one` unit of a component is not a word of
a two-word unit of the segment. -/
theorem oneAt_twoAt_seg {S U : Ty} {o j o' : Nat} {L us : List Acc} (h1 : AtOff S o U) (hL : accs S = some L)
    (hus : accs U = some us) (hj : TermFul.OneAt us j) (htw : TwoAt L o') :
    o + j ≠ o' ∧ o + j ≠ o' + 1 ∧ o + j < nWords L ∧ o' + 2 ≤ nWords L := by
  obtain ⟨pre, post, e, hn⟩ := AtOff_embed h1 hL hus
  obtain ⟨i, hi, rfl⟩ := htw
  have hj' : TermFul.OneAt L (o + j) := by
    rw [e, ← hn, List.append_assoc]; exact oneAtF_prepend pre (oneAtF_append post hj)
  have hsplit := list_split_at L i .two hi
  have hlt := TermFul.OneAt_lt hj'
  rw [hsplit] at hj'
  have h2 := TermGlob.oneAt_split _ _ hj'
  have hnL : nWords L = nWords (L.take i) + 2 + nWords (L.drop (i + 1)) := by
    conv => lhs; rw [hsplit]
    simp only [nWords, List.map_append, List.map_cons, List.sum_append, List.sum_cons, Acc.size]; omega
  omega

/-- **Layout**: a `.one` unit of a component `U` of `T` (at `o`) never covers
either word of a two-word unit of `T` (`TwoAtT`). -/
theorem oneAt_twoAtT {T U : Ty} {o j o2 : Nat} {us : List Acc} (h1 : AtOff T o U) (hus : accs U = some us)
    (hj : TermFul.OneAt us j) (h2 : TwoAtT T o2) : o + j ≠ o2 ∧ o + j ≠ o2 + 1 := by
  obtain ⟨b, S, L, o', hseg, hL, htw, rfl⟩ := h2
  rcases hseg with ⟨rfl, rfl, -⟩ | ⟨N, usS, jj, rfl, husS, hjj, rfl⟩
  · have := oneAt_twoAt_seg h1 hL hus hj htw; omega
  · rw [hL] at husS; cases husS
    rcases AtOff_arr_elem h1 rfl with hU | ⟨us', j', o'', hus', hj', ho, hat⟩
    · subst hU; simp [accs] at hus
    · rw [hL] at hus'; cases hus'
      have hc := oneAt_twoAt_seg hat hL hus hj htw
      subst ho
      rcases Nat.lt_trichotomy j' jj with hlt | rfl | hgt
      · have hm : (j' + 1) * nWords L ≤ jj * nWords L := Nat.mul_le_mul_right _ hlt
        rw [Nat.succ_mul] at hm
        omega
      · omega
      · have hm : (jj + 1) * nWords L ≤ j' * nWords L := Nat.mul_le_mul_right _ hgt
        rw [Nat.succ_mul] at hm
        omega

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **P4b `promNoTwoP`**: the promised address lies in no two-word unit of its
cell.  The promise is fulfilled along the certificate by a single-word write
(`certified_promTypedX`, `SWOne_holds`), a `.one` unit of a component of the
cell (cells keep their type along `Ext`); `oneAt_twoAtT`.  The cell is in the
promiser's cut (`promLocP`; at a label yet to allocate `Eg.sto` is `none`). -/
theorem promNoTwoP_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PromNoTwoPF p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X cl hcl o htw
  obtain ⟨S, hS_S⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hS_S
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hSC : StoClo (Cut Eg j S) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have h0 := InvAtXF_of (p := p) (k := k) (arch := arch) hpi.2.1 hTE
    (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm) hSC (by rw [gOf_promise]; exact X.inv.bf)
    (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh _ _ _ X.hth))
    (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
      (Nat.sub_le_sub_right (by rw [hpi.1]; show c.mem.size ≤ (c.mem.push _).size; rw [Array.size_push]; exact Nat.le_succ _) 1))
  have ht : c.mem.size ∈ TermFul.promsOf (promise c j a v w) j := by
    rw [TermFul.promsOf_some hpi.2.1]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hmt : (promise c j a v w).mem[c.mem.size]? = some ⟨a, v, w⟩ := by
    rw [hpi.1]; exact Array.getElem?_push_size
  have hcut : cutSto Eg j a.label = some cl := by
    rcases promLocP (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X with ⟨cl', hcl'⟩ | ⟨m, hm', hl⟩
    · rw [cutSto_sub hcl'] at hcl; cases hcl; exact hcl'
    · have := (X.inv.fresh j th X.hth m hm').1
      rw [← hl, hcl] at this; cases this
  obtain ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, -, -, -, hIH0⟩ := h0
  have hX : InvAtX p k arch j (Cut Eg j S) _ _ (promise c j a v w) :=
    ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, fun _ _ _ h => h.elim, hIH0⟩
  have hsc := fun c1 h1 h2 => (hrun X S hS_S c1 h1 h2).1
  have hwin := fun c1 h1 h2 => (hrun X S hS_S c1 h1 h2).2
  obtain ⟨c1, c2, th1, th2, ρ, η, cx, E2, -, -, -, -, -, -, hx1, hE, hT, htv, hi, hmi, hscope, hpa, -, -, -, -, -,
    -, -, hsw, -⟩ := certified_promTypedX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hX (TermMain.tidAt_cutP X.inv j S) X.cert ht hmt
  obtain ⟨cl1, o1, U, us, j1, hcl1, h1o, hus, hj, ho⟩ :=
    SWOne_holds p _ _ _ _ ρ η cx _ _ hE hT htv hi hmi (TermTyped.scopeD_SW hscope hsw) hpa hsw
  have e : (Cut Eg j S).sto a.label = some cl := hcut
  rw [hx1.2.2.2.2.1 _ _ e] at hcl1
  cases hcl1
  have hoff : a.offset = o1 + j1 := ho
  rw [hoff]
  exact oneAt_twoAtT h1o hus hj htw

end

#print axioms oneAt_twoAtT
#print axioms promNoTwoP_of

/-! ## The plant choice `plantOf` (F2′)

At a promise step of `j` (promise `B` at `a`), the plant fires at every label
reached from `a.label` by a nonempty chain of `PlantR` edges in the promiser's
cut after the promise: an outstanding promise at a cell whose type has no `own`
or region reference (`noOwnIn`, `rgnFree`) naming an own private cell without frontier.  Only cells without a
frontier qualify (so the plant fires at the first promise naming the cell), and
the chain is the transitive closure (`ClR`).  The frontier is F2′'s
`plantF = max vWr (holder indices)`, and its count `plantN = Np`, both computed at the
promiser's state before the promise (as `TermTyped.certified_hinhW1`'s `plantE`). -/

/-- The promiser's cut, its state after the promise. -/
noncomputable def cutP (Eg : GEnv) (j : Nat) : TEnv := Cut Eg j (fun _ => False)

/-- `l` is planted by the promise of `j` at `a` (from `c`, promiser state `th`). -/
def PlantL (c : Cfg) (Eg : GEnv) (j : Nat) (th : TTh) (a : Address) (v : WeakMem.Val) (w : Ts) (l : AllocLabel) :
    Prop :=
  ∃ l', ClR (PlantR (cutP Eg j) (c.mem.push ⟨a, v, w⟩) (th.promises ++ [c.mem.size])) a.label l' ∧
    PlantR (cutP Eg j) (c.mem.push ⟨a, v, w⟩) (th.promises ++ [c.mem.size]) l' l

open Classical in
/-- **The plant choice.** -/
noncomputable def plantOf (c : Cfg) (Eg : GEnv) (j : Nat) (a : Address) (v : WeakMem.Val) (w : Ts)
    (l : AllocLabel) : Option Ts :=
  match c.ths[j]? with
  | none => none
  | some th => if PlantL c Eg j th a v w l then
      some (plantF (cutP Eg j) (stOf c.mem c.pairs th) l) else none

open Classical in
/-- (B1) **The planted count**: F2′'s `N`, the maximal held prefix (`Np`) in the promiser's
cut before the promise (read by `plantG` only at labels `plantOf` chooses). -/
noncomputable def plantN (c : Cfg) (Eg : GEnv) (j : Nat) (a : Address) (v : WeakMem.Val) (w : Ts)
    (l : AllocLabel) : Nat :=
  match c.ths[j]? with
  | none => 0
  | some th => NpZ (cutP Eg j) (stOf c.mem c.pairs th) l

theorem plantOf_some {c : Cfg} {Eg : GEnv} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    {l : AllocLabel} {f : Ts} (hth : c.ths[j]? = some th) (h : plantOf c Eg j a v w l = some f) :
    PlantL c Eg j th a v w l ∧ f = plantF (cutP Eg j) (stOf c.mem c.pairs th) l := by
  unfold plantOf at h
  rw [hth] at h
  dsimp only at h
  by_cases hp : PlantL c Eg j th a v w l
  · simp only [hp, ite_true, Option.some.injEq] at h; exact ⟨hp, h.symm⟩
  · simp [hp] at h

theorem foldr_max_le {L : List Nat} {n : Nat} (h : ∀ x ∈ L, x ≤ n) : L.foldr max 0 ≤ n := by
  induction L with
  | nil => exact Nat.zero_le _
  | cons x L ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.2 ⟨h x (List.mem_cons_self ..), ih fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The type facts at a planted label, from `plant_typeFacts` at its `PlantR`
edge (in the promised configuration, typed at the promiser's cut). -/
theorem plant_facts (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {l l' : AllocLabel} (hR : PlantR (cutP Eg j) (c.mem.push ⟨a, v, w⟩) (th.promises ++ [c.mem.size]) l' l) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ cl, Eg.sto l = some cl ∧ cl.owner = some j ∧ Eg.pfr l = none ∧
      LayT cl.ty ∧ (∀ b S, SegOf cl.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] cl.ty = true ∧
      Ty.noOwnIn [] cl.ty = true ∧ rgnFree cl.ty = true := by
  obtain ⟨S, hS_S⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hS_S
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hSC : StoClo (Cut Eg j S) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  obtain ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, -, -, -, hIH0⟩ := InvAtXF_of (p := p) (k := k) (arch := arch)
    hpi.2.1 hTE (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm) hSC (by rw [gOf_promise]; exact X.inv.bf)
    (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh _ _ _ X.hth))
    (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
      (Nat.sub_le_sub_right (by rw [hpi.1]; show c.mem.size ≤ (c.mem.push _).size; rw [Array.size_push]; exact Nat.le_succ _) 1))
  have hX : InvAtX p k arch j (Cut Eg j S) _ _ (promise c j a v w) :=
    ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, fun _ _ _ h => h.elim, hIH0⟩
  obtain ⟨t, ht, m, hmt, hl', ⟨ca, hca, hno, hrf⟩, a', g, hv, hal, cl, hcl, hown, hnone⟩ := hR
  have ht' : t ∈ TermFul.promsOf (promise c j a v w) j := by rw [TermFul.promsOf_some hpi.2.1]; exact ht
  have hmt' : (promise c j a v w).mem[t]? = some m := by rw [hpi.1]; exact hmt
  have hca' : (Cut Eg j S).sto m.loc.label = some ca := by rw [hl']; exact hca
  have hcl' : (Cut Eg j S).sto a'.label = some cl := by rw [hal]; exact hcl
  obtain ⟨h1, h2, h3, h4, h5⟩ := plant_typeFacts (hPS := hPS) (hSub := hSub) (hSig := hSig) hP (fun c1 h1 h2 => (hrun X S hS_S c1 h1 h2).1) (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc')
    (fun c1 h1 h2 => (hrun X S hS_S c1 h1 h2).2) hX (TermMain.tidAt_cutP X.inv j S) X.cert ht' hmt' hca' hno hrf hv hcl'
  exact ⟨cl, cutSto_sub hcl, hown, hnone, h1, h2, h3, h4, h5⟩

/-- **P2 `plantSpec`** for `plantOf`: a planted label had no frontier, is an
own cell of the promiser, its frontier is at most memory's size, and its type
is `noOR`. -/
theorem plantSpec_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PlantSpec Eg (plantOf c Eg j a v w) j c.mem.size := by
  intro l f hf
  obtain ⟨⟨l', -, hR⟩, rfl⟩ := plantOf_some X.hth hf
  obtain ⟨cl, hcl, hown, hnone, -, -, -, h4, h5⟩ := plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
  refine ⟨hnone, ⟨cl, hcl, hown⟩, ?_, fun cl' hcl' => ?_⟩
  · unfold plantF plantT
    refine Nat.max_le.2 ⟨X.inv.vwr j th X.hth, foldr_max_le fun u hu => ?_⟩
    have hu' : u ∈ th.promises := (List.mem_filter.1 hu).1
    exact Nat.le_of_lt (X.inv.plt j th u X.hth hu')
  · rw [hcl] at hcl'; cases hcl'
    exact noOR_of _ [] h4 h5

/-- **P4b `plantCpl`** for `plantOf`. -/
theorem plantCpl_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PlantCplF p k arch Sp Init MintOK c0 plantOf := by
  intro c Eg Tot HP HS cr db j th a v w X l f hf cl hcl
  obtain ⟨⟨l', -, hR⟩, -⟩ := plantOf_some X.hth hf
  obtain ⟨cl', hcl', -, -, h1, h2, h3, h4, h5⟩ := plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
  rw [hcl] at hcl'; cases hcl'
  exact ⟨h1, h2, h3, h4, h5⟩

end

#print axioms plantSpec_of
#print axioms plantCpl_of

/-! ## B3: PromTyOK (a0)/(a) across a promise step

Old promises at labels already shared keep their facts (`PubE` only grows: shared
cells stay shared, `ini` only grows, `pfr` is kept, `PlantSpec`); another thread's
promise is never at a planted label (planted labels are the promiser's private
cells, foreign promises are visible, `FpOK`).  What is left are the residual
facts `PromNewOKF` (the new promise, if its label is shared after the step) and
`PlantPromOKF` (the promiser's old promises at a label the step plants), both
certificate facts. -/

/-- (B3 residual) The new promise at a label shared after the step is at an
initialised offset and a typed word there. -/
def PromNewOKF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ cl, Eg.sto a.label = some cl → (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared a.label →
      InitR (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl a.label a.offset ∧
      WordOK (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl.ty a.offset (mw ⟨a, v, w⟩)

/-- (B3 residual) The promiser's old promises at a label the step plants are at
initialised offsets (the planted count) and typed words (the holders' values). -/
def PlantPromOKF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ l f, plantOf c Eg j a v w l = some f → ∀ t m, t ∈ th.promises → c.mem[t]? = some m → m.loc.label = l →
      ∀ cl, Eg.sto l = some cl →
        InitR (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl l m.loc.offset ∧
        WordOK (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl.ty m.loc.offset (mw m)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The common case split of a promise at the promised configuration: the new
promise; an old promise at a label shared before; or the promiser's old promise
at a planted label (a foreign promise is never at a planted label). -/
theorem promP_cases (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {j' : Nat} {th' : TTh} {t : Ts} {m : Msg} (hth' : (promise c j a v w).ths[j']? = some th')
    (ht : t ∈ th'.promises) (hm : (promise c j a v w).mem[t]? = some m)
    (hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared m.loc.label) :
    (t = c.mem.size ∧ m = ⟨a, v, w⟩) ∨
    (∃ th0, c.ths[j']? = some th0 ∧ t ∈ th0.promises ∧ c.mem[t]? = some m ∧ Eg.Shared m.loc.label) ∨
    (t ∈ th.promises ∧ c.mem[t]? = some m ∧ ∃ f, plantOf c Eg j a v w m.loc.label = some f) := by
  obtain ⟨th0, h0, -, hold⟩ := prom_old X.hth hth'
  rw [prom_mem X.hth] at hm
  rcases hold t ht with ht0 | ⟨rfl, rfl⟩
  · have hlt := X.inv.plt j' th0 t h0 ht0
    rcases push_get hm with ⟨-, hm0⟩ | ⟨e, -⟩
    · obtain ⟨f, hf⟩ := hsh
      cases e : plantOf c Eg j a v w m.loc.label with
      | none =>
        have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr m.loc.label = some f := hf
        simp only [plantG, e] at h
        exact .inr (.inl ⟨th0, h0, ht0, hm0, f, h⟩)
      | some f' =>
        by_cases hjj : j' = j
        · subst hjj
          rw [X.hth] at h0; cases h0
          exact .inr (.inr ⟨ht0, hm0, f', rfl⟩)
        · exfalso
          have hnj : t ∉ th.promises := fun h => X.inv.disj j' j th0 th t hjj h0 X.hth ht0 h
          obtain ⟨S, -⟩ := X.inv.thr j th X.hth
          have hfp : t ∈ Eg.fpOf j := by
            rcases List.mem_append.1 ((X.inv.proms j th X.hth t).2 (mem_allProms.2 ⟨j', th0, h0, ht0⟩)) with h | h
            · exact absurd h hnj
            · exact h
          have := plant_none (hspec X) ((X.inv.fpok j th S X.hth).2 t m hfp hm0)
          rw [this] at e; cases e
    · exact absurd (e ▸ hlt) (Nat.lt_irrefl _)
  · rcases push_get hm with ⟨h1, -⟩ | ⟨-, rfl⟩
    · exact absurd h1 (Nat.lt_irrefl _)
    · exact .inl ⟨rfl, rfl⟩

/-- `PubE` grows along the plant. -/
theorem pubE_plant_sto {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}
    (hP : PlantSpec Eg P j n) (l : AllocLabel) (cl : Cell) (h : (PubE Eg).sto l = some cl) :
    (PubE (EgP Eg P N j n)).sto l = some cl := by
  have hsh : Eg.Shared l := by
    by_cases hs : Eg.Shared l
    · exact hs
    · simp [PubE, hs] at h
  obtain ⟨f, hf⟩ := hsh
  have hsh' : (EgP Eg P N j n).Shared l := ⟨f, by
    show (plantG Eg P N).pfr l = some f
    cases e : P l with
    | none => simp only [plantG, e]; exact hf
    | some f' => rw [(hP l f' e).1] at hf; cases hf⟩
  rw [PubE_sto hsh']; rw [PubE_sto ⟨f, hf⟩] at h; exact h

theorem pubE_plant_pfr {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}
    (hP : PlantSpec Eg P j n) (l : AllocLabel) (f : Ts) (h : (PubE Eg).pfr l = some f) :
    (PubE (EgP Eg P N j n)).pfr l = some f := by
  show (plantG Eg P N).pfr l = some f
  have hf : Eg.pfr l = some f := h
  cases e : P l with
  | none => simp only [plantG, e]; exact hf
  | some f' => rw [(hP l f' e).1] at hf; cases hf

theorem wordOK_pubE_plant {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}
    (hP : PlantSpec Eg P j n) {T : Ty} {o : Nat} {ww : Word} (h : WordOK (PubE Eg) T o ww) :
    WordOK (PubE (EgP Eg P N j n)) T o ww :=
  WordOK_mono (η₁ := PubE Eg) (η₂ := PubE (EgP Eg P N j n)) rfl rfl (pubE_plant_sto hP) (plantG_ini_le Eg P N)
    (pubE_plant_pfr (N := N) hP) (fun _ h => h) h

/-- **P4b `promTyAPostP`**, from the clause at the source and the residuals. -/
theorem promTyAPostP_of (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf)
    (hnew : PromNewOKF p k arch Sp Init MintOK c0 plantOf plantN) (hpl : PlantPromOKF p k arch Sp Init MintOK c0 plantOf plantN) :
    PromTyAPostPF p k arch Sp Init MintOK c0 plantOf plantN := by
  intro c Eg Tot HP HS cr db j th a v w X j' th' t m hth' ht hm cl hcl hsh
  have hcl0 : Eg.sto m.loc.label = some cl := hcl
  rcases promP_cases hspec X hth' ht hm hsh with ⟨-, rfl⟩ | ⟨th0, h0, ht0, hm0, hs0⟩ | ⟨ht0, hm0, f, hf⟩
  · exact (hnew X cl hcl0 hsh).2
  · exact wordOK_pubE_plant (hspec X) (X.inv.promTy j' th0 t m h0 ht0 hm0 cl hcl0 hs0)
  · exact (hpl X _ f hf t m ht0 hm0 rfl cl hcl0).2

/-- **P4b `promIniPostP`**, from the clause at the source and the residuals. -/
theorem promIniPostP_of (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf)
    (hnew : PromNewOKF p k arch Sp Init MintOK c0 plantOf plantN) (hpl : PlantPromOKF p k arch Sp Init MintOK c0 plantOf plantN) :
    PromIniPostPF p k arch Sp Init MintOK c0 plantOf plantN := by
  intro c Eg Tot HP HS cr db j th a v w X j' th' t m hth' ht hm cl hcl hsh
  have hcl0 : Eg.sto m.loc.label = some cl := hcl
  rcases promP_cases hspec X hth' ht hm hsh with ⟨-, rfl⟩ | ⟨th0, h0, ht0, hm0, hs0⟩ | ⟨ht0, hm0, f, hf⟩
  · exact (hnew X cl hcl0 hsh).1
  · have h := X.inv.promIni j' th0 t m h0 ht0 hm0 cl hcl0 hs0
    exact fun N e us h1 h2 => Nat.lt_of_lt_of_le (h N e us h1 h2)
      (Nat.mul_le_mul_right _ (plantG_ini_le Eg _ _ _))
  · exact (hpl X _ f hf t m ht0 hm0 rfl cl hcl0).1

end

#print axioms promTyAPostP_of
#print axioms promIniPostP_of

/-! ## B3: PromTyOK (a0)/(a) across a thread step

A label shared after the step was shared before (its frontier is kept; the
`PubE` facts transport: `ini`, `rini` only grow, `pfr` is kept, Σ grows at
fresh labels only, which carry no frontier) or is newly shared by the stepper
(publish or plant: its own cell, frontier from none).  At such a cell only the
stepper's promises lie (foreign promises are visible to the stepper, `FpOK`),
which is the residual `PubPromOKF`. -/

/-- (B3 residual) The stepper's outstanding promises at a cell the step newly
shares are at initialised offsets and typed words. -/
def PubPromOKF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ crS : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) crS (db i) δ →
    (∀ l, TermOwnG0Defs.PubAt th l → ∀ t, crS t = cr i t) →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    ∀ l f, Eg.pfr l = none → E'.pfr l = some f → ∀ t m, t ∈ r.2.2.promises → c'.mem[t]? = some m → m.loc.label = l →
      ∀ cl, Eg.sto l = some cl →
        InitR (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')) cl l m.loc.offset ∧
        WordOK (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')) cl.ty m.loc.offset (mw m)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The case split at a thread step: a promise at a label shared after the step
is an old promise at a label shared before, or a promise of the stepper at a
cell the step newly shares. -/
theorem promT_cases
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {k' : Nat} {thk : TTh} {t : Ts} {m : Msg} (hk : c'.ths[k']? = some thk) (ht : t ∈ thk.promises)
    (hm : c'.mem[t]? = some m) {cl : Cell}
    (hcl : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto m.loc.label = some cl)
    (hsh : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').Shared m.loc.label) :
    Eg.sto m.loc.label = some cl ∧
    ((∃ th0, c.ths[k']? = some th0 ∧ t ∈ th0.promises ∧ c.mem[t]? = some m ∧ Eg.Shared m.loc.label) ∨
     (k' = i ∧ t ∈ r.2.2.promises ∧ Eg.pfr m.loc.label = none ∧ ∃ f, E'.pfr m.loc.label = some f)) := by
  have hF := Z.1
  have hCE : CE η = Cut Eg i S := Y.1
  obtain ⟨S0, -, -, hmi, -⟩ := X.inv.thr i th X.hth
  have hsub : ∀ t, t ∈ r.2.2.promises → t ∈ th.promises := fun t ht =>
    (TermFul.tstep_fulfil (fun t ht => X.inv.plt i th t X.hth ht) (MemInv_nopair hmi) X.hr).1.subset ht
  -- the promise was outstanding at `c`
  obtain ⟨th0, h0, ht0, hk'⟩ : ∃ th0, c.ths[k']? = some th0 ∧ t ∈ th0.promises ∧
      (k' = i → th0 = th ∧ thk = r.2.2) := by
    by_cases hki : k' = i
    · subst hki
      rw [X.e3] at hk; cases hk
      exact ⟨th, X.hth, hsub t ht, fun _ => ⟨rfl, rfl⟩⟩
    · rw [X.ho k' hki] at hk
      exact ⟨thk, hk, ht, fun h => absurd h hki⟩
  have hlt := X.inv.plt k' th0 t h0 ht0
  have hm0 : c.mem[t]? = some m := by
    have e : c.mem[t]? = some c.mem[t] := by simp [hlt]
    have e2 := (TermFul.tstep_grow X.hr).1 t _ e
    rw [← X.e1] at e2; rw [hm] at e2; cases e2; exact e
  -- the label is not a fresh one of the step
  obtain ⟨f, hf⟩ := hsh
  have hfE : E'.pfr m.loc.label = some f := hf
  have hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label := by
    rintro hfr
    rcases hF.2.2.2.2.2.1 m.loc.label with e | ⟨-, F0, -, -, -, ⟨c1, hc1, -⟩, -⟩ | ⟨-, -, hsn⟩
    · obtain ⟨jj, hjj, -, hl⟩ := hfr
      have hl' : m.loc.label = freshLabel c.lbase c.n i jj := hl
      have hg := (X.inv.fresh i th X.hth jj hjj).2.2.2.1
      have e2 : (CE η).pfr m.loc.label = Eg.pfr m.loc.label := by rw [hCE]; rfl
      rw [e, e2, hl', hg] at hfE; cases hfE
    · obtain ⟨jj, hjj, -, hl⟩ := hfr
      have hl' : m.loc.label = freshLabel c.lbase c.n i jj := hl
      have hg := (X.inv.fresh i th X.hth jj hjj).1
      have e2 : (CE η).sto m.loc.label = cutSto Eg i m.loc.label := by rw [hCE]; rfl
      rw [e2, hl'] at hc1
      rw [cutSto_sub hc1] at hg; cases hg
    · have h1 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto m.loc.label = E'.sto m.loc.label := by
        simp [EgT, GEnv.withFp, GEnv.post, hfr]
      rw [h1, hsn] at hcl; cases hcl
  have hsto : Eg.sto m.loc.label = some cl := by
    have h1 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto m.loc.label = Eg.sto m.loc.label := by
      simp [EgT, GEnv.withFp, GEnv.post, hnf]
    rw [← h1]; exact hcl
  refine ⟨hsto, ?_⟩
  have e2 : (CE η).pfr m.loc.label = Eg.pfr m.loc.label := by rw [hCE]; rfl
  rcases hF.2.2.2.2.2.1 m.loc.label with e | ⟨hn0, F0, -, -, -, ⟨cc, hcc, hoc⟩, -⟩ | ⟨hfr, -⟩
  · rw [e, e2] at hfE
    exact .inl ⟨th0, h0, ht0, hm0, f, hfE⟩
  · rw [e2] at hn0
    -- a newly shared cell is a private cell of the stepper: only its promises lie there
    by_cases hki : k' = i
    · obtain ⟨rfl, rfl⟩ := hk' hki
      exact .inr ⟨hki, ht, hn0, f, hfE⟩
    · exfalso
      have hnj : t ∉ th.promises := fun h => X.inv.disj k' i th0 th t hki h0 X.hth ht0 h
      have hfp : t ∈ Eg.fpOf i := by
        rcases List.mem_append.1 ((X.inv.proms i th X.hth t).2 (mem_allProms.2 ⟨k', th0, h0, ht0⟩)) with h | h
        · exact absurd h hnj
        · exact h
      have hv := (X.inv.fpok i th S X.hth).2 t m hfp hm0
      rw [hCE] at hcc hoc
      exact hv ⟨⟨cc, hcc, hoc⟩, by show Eg.pfr _ = none; exact hn0⟩
  · exact absurd hfr hnf


/-- `PubE` grows along a thread step (at labels shared before). -/
theorem pubE_post_facts
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ) :
    (∀ l cl, (PubE Eg).sto l = some cl → (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')).sto l = some cl) ∧
    (∀ l, (PubE Eg).ini l ≤ (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')).ini l) ∧
    (∀ l f, (PubE Eg).pfr l = some f → (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')).pfr l = some f) ∧
    (∀ l B, (PubE Eg).box l = some B → (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')).box l = some B) ∧
    (∀ l, (PubE Eg).rini l ≤ (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')).rini l) := by
  have hF := Z.1
  have hCE : CE η = Cut Eg i S := Y.1
  have hfr0 : ∀ l, FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l →
      Eg.sto l = none ∧ Eg.box l = none ∧ Eg.pfr l = none := fun l hfr => by
    obtain ⟨jj, hjj, -, hl⟩ := hfr
    have hl' : l = freshLabel c.lbase c.n i jj := hl
    obtain ⟨h1, h2, -, h4, -⟩ := X.inv.fresh i th X.hth jj hjj
    rw [hl']; exact ⟨h1, h2, h4⟩
  have hpfr : ∀ l f, Eg.pfr l = some f → E'.pfr l = some f := fun l f hf => by
    have e2 : (CE η).pfr l = Eg.pfr l := by rw [hCE]; rfl
    rcases hF.2.2.2.2.2.1 l with e | ⟨hn0, -⟩ | ⟨hfr, -⟩
    · rw [e, e2]; exact hf
    · rw [e2, hf] at hn0; cases hn0
    · rw [(hfr0 l hfr).2.2] at hf; cases hf
  have hsto : ∀ l cl, Eg.sto l = some cl → (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl :=
    fun l cl h => by
      have hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hfr => by
        rw [(hfr0 l hfr).1] at h; cases h
      simp [EgT, GEnv.withFp, GEnv.post, hnf, h]
  refine ⟨fun l cl h => ?_, fun l => ?_, fun l f h => hpfr l f h, fun l B h => ?_, fun l => ?_⟩
  · have hs : Eg.Shared l := by
      by_cases hs : Eg.Shared l
      · exact hs
      · simp [PubE, hs] at h
    obtain ⟨f, hf⟩ := hs
    rw [PubE_sto ⟨f, hf⟩] at h
    rw [PubE_sto ⟨f, hpfr l f hf⟩]
    exact hsto l cl h
  · have e2 : (CE η).ini l = Eg.ini l := by rw [hCE]; rfl
    have := (hF.2.2.2.2.1 l).1
    rw [e2] at this; exact this
  · have hB : Eg.box l = some B := h
    have hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hfr => by
      rw [(hfr0 l hfr).2.1] at hB; cases hB
    show (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').box l = some B
    simp [EgT, GEnv.withFp, GEnv.post, hnf, hB]
  · have e2 : (CE η).rini l = Eg.rini l := by rw [hCE]; rfl
    have := hF.2.2.2.2.2.2.2.2.2.1 l
    rw [e2] at this; exact this

/-- **T16b `promTyAPost`**, from the clause at the source and `PubPromOKF`. -/
theorem promTyAPost_of (hres : PubPromOKF p k arch Sp Init MintOK c0) : PromTyAPostF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS X Y Z hPub hPfrP hS k' thk t m hk ht hm cl hcl hsh
  have ZC := Z.toC Rf Rs (HP i + HS) (cr i) (db i)
  obtain ⟨hsto, ⟨th0, h0, ht0, hm0, hs0⟩ | ⟨-, ht', hn0, f, hf⟩⟩ := promT_cases X Y ZC hk ht hm hcl hsh
  · obtain ⟨h1, h2, h3, h4, h5⟩ := pubE_post_facts X Y ZC
    exact WordOK_mono (η₁ := PubE Eg) (η₂ := PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')) rfl rfl h1 h2 h3 (fun _ h => h) (X.inv.promTy k' th0 t m h0 ht0 hm0 cl hsto hs0) h4 h5
  · exact (hres X Y Z hPub hPfrP hS _ f hn0 hf t m ht' hm rfl cl hsto).2

/-- **T16b/T16d `promIniPost`**, from the clause at the source and `PubPromOKF`. -/
theorem promIniPost_of (hres : PubPromOKF p k arch Sp Init MintOK c0) : PromIniPostF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS X Y Z hPub hPfrP hS k' thk t m hk ht hm cl hcl hsh
  have ZC := Z.toC Rf Rs (HP i + HS) (cr i) (db i)
  obtain ⟨hsto, ⟨th0, h0, ht0, hm0, hs0⟩ | ⟨-, ht', hn0, f, hf⟩⟩ := promT_cases X Y ZC hk ht hm hcl hsh
  · obtain ⟨-, h2, -⟩ := pubE_post_facts X Y ZC
    have h := X.inv.promIni k' th0 t m h0 ht0 hm0 cl hsto hs0
    exact fun N e us e1 e2 => Nat.lt_of_lt_of_le (h N e us e1 e2) (Nat.mul_le_mul_right _ (h2 _))
  · exact (hres X Y Z hPub hPfrP hS _ f hn0 hf t m ht' hm rfl cl hsto).1

end

#print axioms promTyAPost_of
#print axioms promIniPost_of

/-! ## Run fact: an outstanding promise's view is below its index -/

/-- Every outstanding promise is a message whose view is below its index. -/
def PromViewLt (c : Cfg) : Prop :=
  ∀ (i : Nat) (th : TTh) (t : Ts), c.ths[i]? = some th → t ∈ th.promises → ∃ m : Msg, c.mem[t]? = some m ∧ m.view < t

theorem promViewLt_step {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} (h : PromViewLt c)
    (hs : Step p k arch c c') : PromViewLt c' := by
  cases hs with
  | thread i hc _ =>
    obtain ⟨th, r, hth, hr, e1, -, e3, ho⟩ := threadSteps_upd hc
    obtain ⟨-, hme, hsub, -, -⟩ := TermCert.tstep_appUp hr
    intro i' th' t hi' ht
    by_cases hii : i' = i
    · subst hii
      rw [e3] at hi'; cases hi'
      obtain ⟨m, hm, hv⟩ := h i' th t hth (hsub t ht)
      exact ⟨m, by rw [e1]; exact hme t m hm, hv⟩
    · rw [ho i' hii] at hi'
      obtain ⟨m, hm, hv⟩ := h i' th' t hi' ht
      have hme' := hme t m hm
      exact ⟨m, by rw [e1]; exact hme', hv⟩
  | prom i a v w hi hw _ =>
    obtain ⟨th, hth⟩ : ∃ th, c.ths[i]? = some th := ⟨c.ths[i], Array.getElem?_eq_getElem hi⟩
    have hpi := promise_inv (a := a) (v := v) (w := w) hth
    intro i' th' t hi' ht
    by_cases hii : i' = i
    · subst hii
      rw [hpi.2.1] at hi'; cases hi'
      rcases List.mem_append.1 ht with ht | ht
      · obtain ⟨m, hm, hv⟩ := h i' th t hth ht
        have hlt : t < c.mem.size := TermPlant.lt_size_of_some hm
        refine ⟨m, ?_, hv⟩
        rw [hpi.1]; show (c.mem.push _)[t]? = some m
        rw [Array.getElem?_push_lt hlt]; simpa [hlt] using hm
      · rw [List.mem_singleton] at ht; subst ht
        refine ⟨⟨a, v, w⟩, ?_, hw⟩
        rw [hpi.1]; exact Array.getElem?_push_size
    · rw [promise_other hth hii] at hi'
      obtain ⟨m, hm, hv⟩ := h i' th' t hi' ht
      have hlt : t < c.mem.size := TermPlant.lt_size_of_some hm
      refine ⟨m, ?_, hv⟩
      rw [hpi.1]; show (c.mem.push _)[t]? = some m
      rw [Array.getElem?_push_lt hlt]; simpa [hlt] using hm

/-- (2b, closed form) `PromViewLt` along every `StepsG … Sp` run from `c0`. -/
def PromViewLtR (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg}, TermSpawnStep.StepsG p k arch Sp c0 c → PromViewLt c

/-- **`PromViewLt` along every run from a promise-free configuration**, given the `Sp`-arm
(at `Sp := ⊥`: `fun _ _ h => h.elim`). -/
theorem promViewLtR_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {c0 : Cfg}
    (hSp : ∀ c c', Sp c c' → PromViewLt c → PromViewLt c') (h0 : AllNoProm c0) : PromViewLtR p k arch Sp c0 :=
  fun hr => TermSpawnStep.stepsG_pres (fun _ _ hs h1 => promViewLt_step h1 hs) hSp hr
    (fun i th t hi ht => by rw [h0 i th hi] at ht; cases ht)
#print axioms TermPlantF.promViewLtR_of


theorem promViewLt_run {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {c0 c : Cfg}
    (h0 : PromViewLtR p k arch Sp c0) (hr : TermSpawnStep.StepsG p k arch Sp c0 c) : PromViewLt c := h0 hr

#print axioms promViewLt_run

/-! ## `plantInh` from `certified_hinhW1`

Named run facts (each the restatement of an existing open obligation, not a new one):
- `RunAgreeF`: `TermTyped.RunAgree` for the certificate environments of a promise step
  (the `hres` of `certified_hinhW1`). Its `ini` part is `hIniStab` (route R-b, `ownSeen`), its
  `pfr`/`pay` parts are the corresponding items of certified_hinhW1.
- (`PlantClosF` is gone: a plant edge carries its source cell's `noOwnIn`/`rgnFree`, and the
  shared source cells have them from `PubCpl` or `plant_facts`.)
- `PlantInhWF`: the same conclusion at multi-word slots (W2: `certified_hinhW1` is the one-word
  case W1; the W2 extension is open). -/

theorem np_cut_eq (Eg : GEnv) (j : Nat) (S S' : AllocLabel → Prop) (s : St) (l : AllocLabel) :
    Np (Cut Eg j S) s l = Np (Cut Eg j S') s l := rfl

theorem plantF_cut_eq (Eg : GEnv) (j : Nat) (S S' : AllocLabel → Prop) (s : St) (l : AllocLabel) :
    plantF (Cut Eg j S) s l = plantF (Cut Eg j S') s l := rfl

theorem rgnFree_seg {T S : Ty} {b : Nat} (hs : SegOf T b S) (h : rgnFree T = true) : rgnFree S = true := by
  rcases hs with ⟨-, rfl, -⟩ | ⟨N, us, j, rfl, -⟩
  · exact h
  · simpa [rgnFree] using h

theorem plantOf_of {c : Cfg} {Eg : GEnv} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    {l : AllocLabel} (hth : c.ths[j]? = some th) (h : PlantL c Eg j th a v w l) :
    plantOf c Eg j a v w l = some (plantF (cutP Eg j) (stOf c.mem c.pairs th) l) := by
  unfold plantOf; rw [hth]; dsimp only; simp [h]

theorem plantOf_none {c : Cfg} {Eg : GEnv} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    {l : AllocLabel} (hth : c.ths[j]? = some th) (h : ¬ PlantL c Eg j th a v w l) :
    plantOf c Eg j a v w l = none := by
  unfold plantOf; rw [hth]; dsimp only; simp [h]

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (iniop) The start labels whose counts a promise step's certificate run keeps: the published
cells (`ownSeen`: no `bufInit` reaches them, `TermOwnK5`). -/
def IniZF (Eg : GEnv) (l : AllocLabel) : Prop := Eg.pubd l ∧ Eg.sto l ≠ none

/-- (iniop) The thread step publishes the own cell `l` (the term-level T-split). -/
def PubStepOf (Eg : GEnv) (i : Nat) (th : TTh) (l : AllocLabel) : Prop :=
  ∃ cl y a e rt ws ad g', Eg.sto l = some cl ∧ cl.owner = some i ∧ th.term = .let_ y (.publish a) e ∧
    evalAt th.env a = some (rt, ws) ∧ ws.map (·.val) = [.loc ad g'] ∧ ad.label = l

/-- (iniop) The start labels whose counts a thread step's certificate run keeps: the published
cells and the cell the step publishes. -/
def IniZT (Eg : GEnv) (i : Nat) (th : TTh) (l : AllocLabel) : Prop := IniZF Eg l ∨ PubStepOf Eg i th l

/-- (runAgree) The promise-step locality set: the published cells, and the promiser's own cells
whose own key nobody of the promiser holds (no `bufInit` there, `TermNoBufOwn.noBufF_noKey`). -/
def IniZK (Eg : GEnv) (Tot HP : Nat → Res) (j : Nat) (l : AllocLabel) : Prop :=
  IniZF Eg l ∨ ∃ cl, Eg.sto l = some cl ∧ cl.owner = some j ∧ (Tot j + HP j) (.own l) = 0

/-- (runAgree) The thread-step locality set: `IniZT`, and the stepper's own cells whose own key the
stepper does not hold (`TermNoBufOwn.noBufT_noKey`). -/
def IniZTK (Eg : GEnv) (Tot HP : Nat → Res) (i : Nat) (th : TTh) (l : AllocLabel) : Prop :=
  IniZT Eg i th l ∨ ∃ cl, Eg.sto l = some cl ∧ cl.owner = some i ∧ (Tot i + HP i) (.own l) = 0

/-- (iniop; named run fact, proved in `TermIniOpK` from `CertScopeP`/`CertWinP`) No `bufInit`
along a promise step's certificate run targets a published cell, or an own cell of the promiser whose
own key the promiser does not hold (`IniZK`). -/
def BufInitPubF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j → ∀ th1, c1.ths[j]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ IniZK Eg Tot HP j l

/-- (named run fact, proved in `TermK5Z` from `CertScopeP`/`CertWinP`) No `bufInit` along a
promise step's certificate run targets an own cell of the promiser's cut after the run publishes it
(`TermK5R.bufInitPubFR`). -/
def BufInitPubFR (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w → ∀ (S : AllocLabel → Prop),
    ∀ c1 th1 c1' c3 th3 l cl, TermOwnG0Defs.SoloNP p k arch j l (promise c j a v w) c1 → c1.ths[j]? = some th1 →
      TermOwnG0Defs.PubAt th1 l → c1' ∈ threadSteps p k arch c1 j → Solo p k arch j c1' c3 →
      Certified p k arch c3 j → c3.ths[j]? = some th3 → (Cut Eg j S).sto l = some cl →
      cl.owner = some (Cut Eg j S).tid → ¬ BufInitOn th3 l

/-- (iniop; named run fact, proved in `TermIniOpK` from `CertScopeC`/`CertWinC`) No `bufInit`
along a thread step's certificate run targets a published cell, the cell the step publishes, or an own
cell of the stepper whose own key the stepper does not hold (`IniZTK`). -/
def BufInitPubT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
    ∀ c1, Solo p k arch i c' c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ IniZTK Eg Tot HP i th l

/-- (runAgree; named run fact, proved in `TermBufPubT` from `CertScopeC`/`CertWinC`) No `bufInit`
along a thread step's certificate run (from `c'`) targets an own cell of the post-step environment
with a frontier after the run publishes it (`TermNoBufOwn.noBufT_pub`). -/
def BufInitPubTR (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ c1 th1 c1' c3 th3 l cl f, TermOwnG0Defs.SoloNP p k arch i l c' c1 → c1.ths[i]? = some th1 →
      TermOwnG0Defs.PubAt th1 l → c1' ∈ threadSteps p k arch c1 i → Solo p k arch i c1' c3 →
      Certified p k arch c3 i → c3.ths[i]? = some th3 → E'.sto l = some cl → cl.owner = some E'.tid →
      E'.pfr l = some f → ¬ BufInitOn th3 l

/-- (named run fact; = `hIniStab` + the `pfr`/`pay` items) `RunAgree` for the
certificate environments of a promise step, at the promiser's cut (any seen set). -/
def RunAgreeF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ (S : AllocLabel → Prop) c2 th2 E2, Solo p k arch j (promise c j a v w) c2 → Certified p k arch c2 j →
      c2.ths[j]? = some th2 → Ext (Cut Eg j S) E2 → MemInv (gOf p k arch c2 j) E2 (stOf c2.mem c2.pairs th2) →
      FrBound (Cut Eg j S) (c.mem.size + 1) th.vs.vWr E2 → TermTyped.IniLoc (IniZK Eg Tot HP j) (Cut Eg j S) E2 →
      TermTyped.IniHeld (TermTyped.WitP c.mem th.promises) (Cut Eg j S) E2 th2.vs.vWr →
      TermK5Defs.PfrProvE p k arch j (TermTyped.WitP c.mem th.promises) (Cut Eg j S) (promise c j a v w) c2 E2 →
      TermK5O.PfrProvO p k arch j (TermTyped.WitP c.mem th.promises) (Cut Eg j S) (promise c j a v w) c2 E2 →
      TermIni.RunAgreeW (Cut Eg j S) (plantE (Cut Eg j S) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w))
        (PlantL c Eg j th a v w) E2

/-- (named; W2) `PlantInhF` at multi-word slots (`1 < nWords`; zero-width slots are
`plantInhZ`, one-word slots `certified_hinhW1`). -/
def PlantInhWF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' (Sj : AllocLabel → Prop) l f cl b S us, plantOf c Eg j a v w l = some f → Eg.sto l = some cl →
      SegOf cl.ty b S → accs S = some us → 1 < nWords us → ¬ IniSegN (Eg.ini l) cl b →
      IniSeg (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) cl l b →
      ∃ ws, ValOf (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) S ws ∧
        ws.length = nWords us

/-- The planted start environment (`plantE` of TermTyped) sits inside every planted cut. -/
theorem inclS_plantE
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (S0 : AllocLabel → Prop) (j' : Nat) (Sj : AllocLabel → Prop) :
    InclS (plantE (Cut Eg j S0) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w))
      (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) := by
  refine ⟨rfl, fun l2 c2 f2 hc2 hf2 => ?_, fun l2 => ?_, fun l2 f2 hf2 => ?_, fun _ _ h => h, fun _ => Nat.le_refl _⟩
  · have hc2' : Eg.sto l2 = some c2 := cutSto_sub hc2
    refine cutSto_some.2 ⟨hc2', .inr ?_⟩
    by_cases hL : PlantL c Eg j th a v w l2
    · exact ⟨plantF (cutP Eg j) (stOf c.mem c.pairs th) l2,
        by show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l2 = _
           simp only [plantG, plantOf_of X.hth hL]⟩
    · have hf : Eg.pfr l2 = some f2 := by
        have := hf2; simp only [plantE, hL, ite_false] at this; exact this
      exact ⟨f2, by show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l2 = _
                    simp only [plantG, plantOf_none X.hth hL]; exact hf⟩
  · by_cases hL : PlantL c Eg j th a v w l2
    · rw [plantE_ini_in hL]
      show _ ≤ (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).ini l2
      simp only [plantG, plantOf_of X.hth hL, plantN, X.hth]
      exact Nat.le_refl _
    · show (plantE (Cut Eg j S0) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)).ini l2 ≤ _
      simp only [plantE, hL, ite_false]
      exact plantG_ini_le Eg _ _ l2
  · by_cases hL : PlantL c Eg j th a v w l2
    · rw [plantE_pfr_in hL] at hf2; cases hf2
      show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l2 = _
      simp only [plantG, plantOf_of X.hth hL]
      rfl
    · have hf : Eg.pfr l2 = some f2 := by
        have := hf2; simp only [plantE, hL, ite_false] at this; exact this
      show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l2 = _
      simp only [plantG, plantOf_none X.hth hL]; exact hf

/-- (Z-alt (a)) The bare environment of a program sits inside every environment of it. -/
theorem inclS_bare (E : TEnv) : InclS ({ prog := E.prog } : TEnv) E := by
  refine ⟨rfl, ?_, fun _ => Nat.zero_le _, ?_, ?_, fun _ => Nat.zero_le _⟩
  · intro _ _ _ h; cases h
  · intro _ _ h; cases h
  · intro _ _ h; cases h

#print axioms inclS_bare

/-- (Z-alt (a)) **`PlantInhF` at zero-width slots**: a planted buffer of
uninhabited zero-width elements is not raised (`NpZ`), and an inhabited element type
has a value of no words in every environment of the program (`InhZ`, `ValOf_transferS`). -/
theorem plantInhZ (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (j' : Nat) (Sj : AllocLabel → Prop) (l : AllocLabel) (f : Ts) (cl : Cell) (b : Nat) (S : Ty) (us : List Acc)
    (hpl : plantOf c Eg j a v w l = some f) (hcl0 : Eg.sto l = some cl) (hseg : SegOf cl.ty b S)
    (hus : accs S = some us) (h0 : nWords us = 0) (hnot : ¬ IniSegN (Eg.ini l) cl b)
    (hini : IniSeg (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) cl l b) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ ws, ValOf (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) S ws ∧
      ws.length = nWords us := by
  obtain ⟨hPL, -⟩ := plantOf_some X.hth hpl
  obtain ⟨lp, -, hRp⟩ := id hPL
  obtain ⟨clp, hclp, -, -, -, -, -, h4, h5⟩ := plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hRp
  rw [hcl0] at hclp; cases hclp
  have hnS := noOwn_seg hseg h4
  have hrS := rgnFree_seg hseg h5
  have hcP : (cutP Eg j).sto l = some cl := by
    obtain ⟨-, -, t, -, m, -, -, -, a1, g, -, hal, cl1, hc1, -, -⟩ := hPL
    subst hal
    have e1 : cl1 = cl := by rw [cutSto_sub hc1] at hcl0; cases hcl0; rfl
    subst e1; exact hc1
  rcases hseg with ⟨-, rfl, hA⟩ | ⟨N, us2, j0, hT, hus2, -, rfl⟩
  · exact absurd (fun N e hT => by rw [hT] at hA; simp [accs] at hA) hnot
  rw [hus] at hus2; cases hus2
  by_cases hE : EmptyZ (cutP Eg j) l
  · -- not raised: the planted count is the old one
    exfalso
    apply hnot
    have e : (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj).ini l =
        Eg.ini l := by
      show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).ini l = _
      simp only [plantG, hpl, plantN, X.hth]
      rw [NpZ_of_empty hE]
      exact Nat.max_eq_left (Nat.zero_le _)
    unfold IniSeg at hini
    rw [e] at hini
    exact hini
  · obtain ⟨ws, hv, hlen⟩ : InhZ (cutP Eg j).prog S :=
      Classical.byContradiction fun hn => hE ⟨cl, N, S, us, hcP, hT, hus, h0, hn⟩
    refine ⟨ws, ValOf_transferS (inclS_bare _) (noOR_of S [] hnS hrS) hv, ?_⟩
    rw [hlen, h0]

#print axioms plantInhZ

/-- **P4b `plantInh`** for `plantOf`/`plantN`: one-word slots by `certified_hinhW1`. -/
theorem plantInh_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0) (h0 : TermPlantF.PromViewLtR p k arch Sp c0)
    (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0) (hbr : BufInitPubFR p k arch Sp Init MintOK c0)
    (hwide : PlantInhWF p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PlantInhF p k arch Sp Init MintOK c0 plantOf plantN := by
  intro c Eg Tot HP HS cr db j th a v w X j' Sj l f cl b S us hpl hcl0 hseg hus hnot hini
  by_cases h1 : nWords us = 1
  rotate_left
  · by_cases h0 : nWords us = 0
    · exact plantInhZ (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X j' Sj l f cl b S us hpl hcl0 hseg hus h0 hnot hini
    · exact hwide X j' Sj l f cl b S us hpl hcl0 hseg hus (by omega) hnot hini
  obtain ⟨hPL, -⟩ := plantOf_some X.hth hpl
  obtain ⟨S0, hS_S0⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hS_S0
  have hSC : StoClo (Cut Eg j S0) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  obtain ⟨c'', hsolo, hn⟩ := X.cert
  have hc'' : Certified p k arch c'' j := ⟨c'', .refl _, hn⟩
  -- the cell facts of a planted label (its last `PlantR` edge)
  have hLc : ∀ l1, PlantL c Eg j th a v w l1 →
      ∃ cl1, cutSto Eg j l1 = some cl1 ∧ cl1.owner = some j ∧ Eg.pfr l1 = none := fun l1 h => by
    obtain ⟨-, -, t, -, m, -, -, -, a', g, -, hal, cl1, hc1, ho1, hn1⟩ := h
    subst hal
    exact ⟨cl1, hc1, ho1, hn1⟩
  obtain ⟨cl1, hc1, -, -⟩ := hLc l hPL
  have e1 : cl1 = cl := by rw [cutSto_sub hc1] at hcl0; cases hcl0; rfl
  subst e1
  obtain ⟨lp, -, hRp⟩ := id hPL
  obtain ⟨clp, hclp, -, -, -, -, -, h4, h5⟩ := plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hRp
  rw [hcl0] at hclp; cases hclp
  have hnS := noOwn_seg hseg h4
  have hrS := rgnFree_seg hseg h5
  have hpv := promViewLt_run h0 X.run
  obtain ⟨ws, hv, hlen⟩ := TermIni.certified_hinhW1HP (hPS := hPS) (hSub := hSub) (hSig := hSig) (E0 := Cut Eg j S0)
    (hrc0 := X.inv.riniCoh _ _ _ X.hth) (hfl0 := fun l cl f hs hp => X.inv.frlt l cl f (cutSto_sub hs) hp) (Lp := PlantL c Eg j th a v w)
    (Z := IniZK Eg Tot HP j) (hZp := hbr X S0) (hZr := hbp X) hP
    (fun c1 h1 h2 => (hrun X S0 hS_S0 c1 h1 h2).1) (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') (fun c1 h1 h2 => (hrun X S0 hS_S0 c1 h1 h2).2) X.hth hTE hm hSC X.inv.bf
    (fun l => X.inv.rle l)
    (TermMain.tidAt_cut X.inv j S0) hsolo hc''
    (fun l1 h => by obtain ⟨cl2, hc2, ho2, -⟩ := hLc l1 h; exact ⟨cl2, hc2, ho2⟩)
    (fun l1 h => by obtain ⟨-, -, -, hn1⟩ := hLc l1 h; exact hn1)
    (fun l1 hl1 u hu m hm hl a' g hv cl2 hc2 ho2 hn2 => by
      have hlt : u < c.mem.size := TermPlant.lt_size_of_some hm
      have hmp : (c.mem.push ⟨a, v, w⟩)[u]? = some m := by
        rw [Array.getElem?_push_lt hlt]; simpa [hlt] using hm
      have hsh1 : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared l1 :=
        ⟨plantF (cutP Eg j) (stOf c.mem c.pairs th) l1,
          by show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l1 = _
             simp only [plantG, plantOf_of X.hth hl1]⟩
      obtain ⟨l2, h2, hR⟩ := id hl1
      obtain ⟨ca, hca, hoa, -, -, -, -, hno, hrf⟩ := plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
      exact ⟨l1, ClR.step h2 hR, ⟨u, List.mem_append_left _ hu, m, hmp, hl, ⟨ca, cutSto_own hca hoa, hno, hrf⟩,
        a', g, hv, rfl, cl2, hc2, ho2, hn2⟩⟩)
    (fun a2 cl2 hc2 hn2 => by
      rcases (cutSto_some.1 hc2).2 with h | ⟨f2, hf2⟩
      · exact h
      · have hn2' : Eg.pfr a2 = none := hn2
        rw [hn2'] at hf2; cases hf2)
    (fun u hu m hm => by
      obtain ⟨m', hm', hvl⟩ := hpv j th u X.hth hu
      rw [hm] at hm'; cases hm'
      exact Nat.lt_trans hvl (TermPlant.lt_size_of_some hm))
    (fun c2 th2 E2 h2 hc2 hth2 hx2 hm2 hfb2 hB2 hIL2 hIH2 hPV2 hPO2 =>
      TermIni.RunAgree_ofW (hagree X S0 c2 th2 E2 h2 hc2 hth2 hx2 hm2 hfb2 hIL2 hIH2 hPV2 hPO2)
      (TermIni.runAgree_pfrL hB2 (MemInv_promLt hm) (fun l c h => hx2.2.2.2.2.1 l c h)
        (fun l1 h => by obtain ⟨cl2, hc2, -, -⟩ := hLc l1 h; exact ⟨cl2, hc2⟩)
        (fun l1 h => by obtain ⟨-, -, -, hn1⟩ := hLc l1 h; exact hn1)))
    hPL hc1 hseg hus h1 hnS hrS
    (by
      have e : (plantE (Cut Eg j S0) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)).ini l =
          (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj).ini l := by
        rw [plantE_ini_in hPL]
        show _ = (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).ini l
        simp only [plantG, hpl, plantN, X.hth]
        rfl
      unfold IniSeg at hini ⊢; rw [e]; exact hini)
    hnot
  exact ⟨ws, ValOf_transferS (inclS_plantE X S0 j' Sj) (noOR_of S [] hnS hrS) hv, hlen⟩

end

#print axioms plantInh_of

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}

/-! ## SWIni: a typed single-word write lands at an initialised offset

`SWOne_holds` (TermTyped) places an `SW` on a `.one` unit of a component of the
target cell.  The same derivations also carry the component's `IniAt` (`VR (.loc μ u)`
and `slot_view`): the write lands at an initialised offset, at the count
`modeIni μ ≤ ini`, except for `bufInit` (which writes the next uninitialised
slot).  Per-op copies of the `*_ua` lemmas with that conjunct kept. -/

/-- `UnitsAt` with the component's initialisation. -/
def UnitsAtI (η : TEnv) (b : Address) (us : List Acc) : Prop :=
  ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ accs U = some us ∧ IniAt η.ini c b U

theorem modeIni_le (μ : Mode) (η : TEnv) : ∀ l, modeIni μ η.ini η.rini l ≤ η.ini l := by
  intro l; cases μ <;> simp [modeIni] <;> omega

theorem ptr_targetI {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧ IniAt η.ini c b U := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VR hvars hp
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rcases ht with rfl | rfl
  · simp only [VR] at hv
    obtain ⟨a', c, hws, hoff, hsto, hcty, -, hacc⟩ := hv
    have hpw : pw.val = .loc a' 0 := by simpa using hws
    have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
    subst e
    refine ⟨c, c.ty, hsto, ?_, hcty, fun N e hc => ?_⟩
    · rw [hoff]; exact Fd_AtOff Fd.refl hacc
    · rw [hc] at hacc; simp [accs] at hacc
  · simp only [VR] at hv
    rcases hv with ⟨hws, -⟩ | ⟨a', c, U, hws, hsto, hat, hFd, -, hini⟩
    · have hpw : pw.val = .null := by simpa using hws
      simp [addrOf, hpw] at hb
    · have hpw : pw.val = .loc a' 0 := by simpa using hws
      have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
      subst e
      exact ⟨c, U, hsto, hat, hFd, IniAt_mono (modeIni_le μ η) hini⟩

theorem cell_uaI {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {a : At} {t u rt ru : Ty} {μ μr : Mode} {pw : Word} {b : Address}
    {us : List Acc}
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hp : cx.peek a = .ok t) (hc : cellOf t = some (μ, u)) (ho : cx.opaqueOK u = true)
    (hea : evalAt env a = some (rt, [pw])) (hcr : cellOf rt = some (μr, ru)) (hb : addrOf pw = some b)
    (hus : accs ru = some us) : UnitsAtI η b us := by
  obtain ⟨c, U, hsto, hat, hFd, hini⟩ := ptr_targetI hi.2.1 hp (cell_cases hc) hea hb
  have hacc : accs U = some us := by
    rw [Fd_accs hFd, ← pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hp hc ho hea hcr,
      hus]
  exact ⟨_, _, hsto, hat, hacc, hini⟩

theorem store_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {rl : Bool} {a v : At}
    {tok : Option At} {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.store rl a v tok) c') (hsc : OpScope cx (.store rl a v tok))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.store rl a v tok) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | storeOwn hp _ hc _ hu' hsub _ =>
      exact cell_uaI hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus
  | storePub hp _ hc _ hu' hsub _ _ =>
      exact cell_uaI hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus
  | storeRgn hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeCap hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeWordGive hp hw | storeWordKeep hp hw | storeWordHand hp hw =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      rcases ht with rfl | rfl
      · exact cell_uaI hi hE htv hp rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea hcr hb hus
      · exact cell_uaI hi hE htv hp rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea hcr hb hus

theorem xchg_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {a v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchg a v) c') (hsc : OpScope cx (.xchg a v))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchg a v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | xchg hp hx hu' hsub _ =>
      cases hx with
      | rgn _ hc _ _ _ => exact absurd hc (hsc _ hp _ _)
      | own _ hc _ =>
          exact cell_uaI hi hE htv hp hc (sub_opaqueOK (hsub.elim id id)
            (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus

theorem xchgAt_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAt bb i v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAt bb i v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, hea, hei, -, hbe, hnj, hb, hus, rfl⟩ := hu
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, c, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, -, hini, -, -,
        htb, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      exact ⟨_, _, hsto, hat, (buf_accs hi hE hp hbuf ho htb hea hbe).symm.trans hus,
        IniAt_mono (modeIni_le _ η) hini⟩

theorem xchgAtF_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At} {q : List Nat}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAtF bb i q v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAtF bb i q v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, us0, c0, o0, hea, hei, -, hbe, hnj, hb, hus0, hco0, hus, rfl⟩ :=
    hu
  cases hop with
  | xchgAtF hp hbuf hct hopu _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, cc, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, -, -,
        hsku, hsig, htbu, hiniV⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hopu
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus0] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      obtain ⟨cR, o, hco, -, -, -, hato⟩ := compOff_rt q _ _ u0 us0 hct hsku hsig hus0
      rw [hco0] at hco
      simp only [Option.some.injEq, Prod.mk.injEq] at hco
      obtain ⟨rfl, rfl⟩ := hco
      refine ⟨_, _, hsto, ?_, (accs_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho
        (lt_of_guardT (TermStep.tb_compTy q _ _ hct htbu) hi.2.2.2.2.1)).symm.trans
        ((accs_of_elyt (compOff_lyt q _ _ u0 c0 o0 hct hsku (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2
          hco0)).symm.trans hus), ?_⟩
      · simpa [offs, Nat.add_assoc] using AtOff_trans hat hato
      · have h := IniAt_mono (modeIni_le _ η) (hiniV _ _ hato)
        simpa [offs, Nat.add_assoc] using h

theorem stl_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stl bb i v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stl bb i v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rfl, rt, t1, t2, iws, vs, μ0, u0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, hbe, hnj, -,
    hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stl hp hbuf hlo hint hlt hltk _ _ _ =>
      obtain ⟨t, u, n, k, jj, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jj q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i jj ∧
          LtI cx jj (.smul q.2.lanes n) ∧ LtI cx jj (.smul q.2.lanes k) :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu hlt hltk
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wwi, hei', hwi, -⟩ := atom_num hi.2.1 hpi hti
      have hJ0 : ev ρ jj < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
      have hJk0 : ev ρ jj < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
      have hJ : ev ρ jj / w.lanes < ev ρ n :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
      have hJk : ev ρ jj / w.lanes < ev ρ k :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
      obtain ⟨rt', pw', ad, c, μr, ur, us', hea', hwv, hbe', hus', hsto, hat, -, hini, hsku, -⟩ :=
        slot_viewN (ev ρ jj / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [lanesOf, Option.some.injEq, Prod.mk.injEq] at hlo0
      obtain ⟨rfl, rfl⟩ := hlo0
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jj / w.lanes * nWords [Acc.one] = ev ρ jj / w.lanes := by simp [nWords, Acc.size]
      rw [e1] at hat hini
      exact ⟨_, _, hsto, hat, by simp [cl, accs], IniAt_mono (modeIni_le _ η) hini⟩

theorem stlw_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb wi jl v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stlw bb wi jl v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stlw bb wi jl v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rfl, rt, t1, t2, t3, iws, jws, vs, μ0, u0, i0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, -,
    hbe, hni, -, -, hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk _ _ _ _ _ =>
      obtain ⟨t, u, n, k, jw, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jw q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
          LtI cx jw n ∧ LtI cx jw k :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨rt', w', ad, c, μr, ur, us', rti, wwi, hea', hwv, hei', hni', hbe', hus', hsto, hat, -, hini,
        hsku, -, -, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hni] at hni'
      simp only [Option.some.injEq] at hni'
      subst hni'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
      rw [e1] at hat hini
      exact ⟨_, _, hsto, hat, by simp [cl, accs], IniAt_mono (modeIni_le _ η) hini⟩

theorem tgt_swI {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b)
    (hacc : accs (cl ρ η.wit 0 0 u) = some [.one]) : UnitsAtI η b [.one] := by
  obtain ⟨c, U, hsto, hat, hFd, hini⟩ := ptr_targetI hvars hp ht hea hb
  exact ⟨c, U, hsto, hat, (Fd_accs hFd).trans hacc, hini⟩

/-- A component's initialised units: a write at unit `j` of a component with `IniAt`
lies at an `InitR` offset. -/
theorem unitsAtI_initR {η : TEnv} {b : Address} {us : List Acc} {j : Nat} (h : UnitsAtI η b us)
    (hj : TermFul.OneAt us j) : ∃ c, η.sto b.label = some c ∧ InitR η c b.label (b.offset + j) := by
  obtain ⟨c, U, hsto, hat, hus, hini⟩ := h
  refine ⟨c, hsto, fun N e use hT huse => ?_⟩
  have hjl := TermFul.OneAt_lt hj
  rcases hini N e hT with ⟨rfl, -⟩ | ⟨use', jj, o, huse', hjj, ho, hato⟩
  · rw [hT] at hus; simp [accs] at hus
  · rw [huse] at huse'; cases huse'
    obtain ⟨pre, post, e1, e2⟩ := AtOff_embed hato huse hus
    have hn : nWords use = nWords pre + nWords us + nWords post := by
      rw [e1, nWords_append, nWords_append]
    have hm : (jj + 1) * nWords use ≤ η.ini b.label * nWords use := Nat.mul_le_mul_right _ hjj
    rw [Nat.succ_mul] at hm
    omega

theorem fetch_swI {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool}
    {a v : At} {t : Ty} {pw : Word} {loc : Address}
    (hop : OpT p cx x (.fetch o acq rel a v) c') (hsc : OpScope cx (.fetch o acq rel a v))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env a = some (t, [pw])) (hb : addrOf pw = some loc) : UnitsAtI η loc [.one] := by
  cases hop with
  | fetchCell hp _ hc =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_swI hi.2.1 hp (cell_cases hc) hea hb (by simp [cl, accs])
      · exact tgt_swI hi.2.1 hp (cell_cases hc) hea hb (by simp [cl, accs])
  | fetchEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      have hμ := word_mode ht ht' hμ'
      exact tgt_swI hi.2.1 hp ht hea hb
        (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep])
  | fetchShare hp hw _ _ _ hok =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      simp only [fetchOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact tgt_swI hi.2.1 hp ht hea hb (by simp [cl, accs, hok.1.1.1.1])

theorem cas_swI {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {acq rel : Bool} {w e v : At} {tn : String}
    {ok fail : Expr} {t : Ty} {pw : Word} {loc : Address}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail)) (hsc : StepScope cx (.cas acq rel w e v tn ok fail))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env w = some (t, [pw])) (hb : addrOf pw = some loc) : UnitsAtI η loc [.one] := by
  cases hT with
  | casCell hp _ hc hraw =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_swI hi.2.1 hp (cell_cases hc) hea hb (accs_cl_one hraw)
      · exact tgt_swI hi.2.1 hp (cell_cases hc) hea hb (accs_cl_one hraw)
  | casShare hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_swI hi.2.1 hp ht hea hb (by simp [cl, accs, hg])
  | casTake hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_swI hi.2.1 hp ht hea hb (by simp [cl, accs, hg])
  | casEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      rcases hsc _ hp with ⟨μ', r', P', ht', hμ'⟩ | ⟨u, -, hnw⟩
      · have hμ := word_mode ht ht' hμ'
        exact tgt_swI hi.2.1 hp ht hea hb
          (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep])
      · rw [hw] at hnw; cases hnw

theorem unitsOp_uaI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {op : Op}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x op c') (hsc : OpScope cx op)
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s op pw b rel us ws) :
    UnitsAtI η b us ∨ ∃ bb i v, op = .bufInit bb i v := by
  cases op
  case store => exact .inl (store_uaI hop hsc hi hE htv hu)
  case xchg => exact .inl (xchg_uaI hop hsc hi hE htv hu)
  case xchgAt => exact .inl (xchgAt_uaI hop hi hE htv hu)
  case xchgAtF => exact .inl (xchgAtF_uaI hop hi hE htv hu)
  case bufInit bb i v => exact .inr ⟨bb, i, v, rfl⟩
  case stl => exact .inl (stl_uaI hop hi htv hu)
  case stlw => exact .inl (stlw_uaI hop hi htv hu)
  all_goals simp [TermFul.UnitsOp] at hu

/-- **SWIni**: a single-word write of a typed, in-scope thread lands at an
initialised offset of its cell (`InitR`), unless it is a `bufInit`. -/
theorem SWIni {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {loc : Address} {val : WeakMem.Val}
    (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term) (hsw : TermFul.SW g mem pairs th loc val) :
    (∃ c, η.sto loc.label = some c ∧ InitR η c loc.label loc.offset) ∨
      ∃ x bb i v e, th.term = .let_ x (.bufInit bb i v) e := by
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, -, -, hb, -⟩
  · have hT' := hT
    rw [hterm] at hT' hsc
    cases hT' with
    | let_ hop _ =>
        rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, rfl, -⟩ |
            ⟨o, acq, rel, a, v, t, t', pw, nw, tr, mr, rfl, hea, -, hb, -⟩
        · rcases unitsOp_uaI hop hsc hi hE htv hu with hU | ⟨bb, i, v, rfl⟩
          · obtain ⟨c, hc, hI⟩ := unitsAtI_initR hU hj
            exact .inl ⟨c, hc, by simpa [offs] using hI⟩
          · exact .inr ⟨x, bb, i, v, e, hterm⟩
        · obtain ⟨c, hc, hI⟩ := unitsAtI_initR (fetch_swI hop hsc hi hE htv hm hea hb) (.here _)
          exact .inl ⟨c, hc, by simpa using hI⟩
  · rw [hterm] at hT hsc
    obtain ⟨c, hc, hI⟩ := unitsAtI_initR (cas_swI hT hsc hi hE htv hm hea hb) (.here _)
    exact .inl ⟨c, hc, by simpa using hI⟩

end

#print axioms SWIni

/-! ## PromNewOKF, InitR half -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (named run fact; = route R-b `ownSeen` at published own cells, plus F2′ P3 at planted cells)
A `bufInit` the promiser runs along the certificate of a promise step, fulfilling the new promise
at a label shared after the step, writes an offset initialised in the planted global count.  At a
start-published own cell, `ownSeen` excludes the own handle a `bufInit` needs.  At a planted cell
a `bufInit` beyond the planted count `N` appends, which kills the planting promise (P3). -/
def BufInitIniF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ t m, t ∈ th.promises ++ [c.mem.size] → (c.mem.push ⟨a, v, w⟩)[t]? = some m →
    ∀ c1 th1 x bb i v' e, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j → c1.ths[j]? = some th1 →
      th1.term = .let_ x (.bufInit bb i v') e → t ∈ th1.promises →
      ∀ cl, Eg.sto m.loc.label = some cl →
        (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared m.loc.label →
        InitR (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl m.loc.label m.loc.offset

/-- (shared; `promIniGen`'s count comparison) **A certificate count at a label shared after a
promise step is at most the planted global count** (`RunAgree.ini`, at any certificate environment). -/
theorem plantIni_le (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {S0 : AllocLabel → Prop} {E2 : TEnv} {L : AllocLabel} {cl : Cell} (hcl : Eg.sto L = some cl)
    (hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared L)
    (hag : TermIni.RunAgreeW (Cut Eg j S0) (plantE (Cut Eg j S0) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w))
      (PlantL c Eg j th a v w) E2) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    (Cut Eg j S0).sto L = some cl ∧
      E2.ini L ≤ (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)).ini L := by
  have hcl0 : (Cut Eg j S0).sto L = some cl := by
    rcases hsh with ⟨f, hf⟩
    cases e : plantOf c Eg j a v w L with
    | none =>
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr L = some f := hf
      simp only [plantG, e] at h
      exact cutSto_shared hcl ⟨f, h⟩
    | some f' =>
      obtain ⟨-, ⟨cl2, hc2, ho2⟩, -⟩ := plantSpec_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X L f' e
      rw [hcl] at hc2; cases hc2
      exact cutSto_own hcl ho2
  refine ⟨hcl0, ?_⟩
  rcases hsh with ⟨f, hf⟩
  by_cases hL : PlantL c Eg j th a v w L
  · have h1 := hag.ini L (.inr hL)
    rw [plantE_ini_in hL] at h1
    refine Nat.le_trans h1 ?_
    show _ ≤ (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).ini L
    simp only [plantG, plantOf_of X.hth hL, plantN, X.hth]
    exact Nat.le_refl _
  · have hn := plantOf_none X.hth hL
    have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr L = some f := hf
    simp only [plantG, hn] at h
    have h1 := hag.ini L (.inl ⟨cl, f, hcl0, h⟩)
    have e2 : (plantE (Cut Eg j S0) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)).ini L =
        Eg.ini L := by simp only [plantE, hL, ite_false]; rfl
    rw [e2] at h1
    exact Nat.le_trans h1 (plantG_ini_le Eg _ _ _)

/-- **InitR of a promise at a label shared after a promise step** (the new promise or an old one
of the promiser): at an initialised offset of the planted global count. -/
theorem promIniGen (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0) (hbr : BufInitPubFR p k arch Sp Init MintOK c0) (hbuf : BufInitIniF p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {t : Ts} {m : Msg} (htm : t ∈ th.promises ++ [c.mem.size]) (hmm : (c.mem.push ⟨a, v, w⟩)[t]? = some m)
    (cl : Cell) (hcl : Eg.sto m.loc.label = some cl)
    (hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared m.loc.label) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    InitR (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl m.loc.label m.loc.offset := by
  obtain ⟨S0, hS_S0⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hS_S0
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hSC : StoClo (Cut Eg j S0) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have h0 := InvAtXFP_of (p := p) (k := k) (arch := arch) hpi.2.1 hTE
    (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm) hSC (by rw [gOf_promise]; exact X.inv.bf)
    (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh _ _ _ X.hth))
    (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
      (Nat.sub_le_sub_right (by rw [hpi.1]; show c.mem.size ≤ (c.mem.push _).size; rw [Array.size_push]; exact Nat.le_succ _) 1)) (IniZK Eg Tot HP j)
    (TermTyped.WitP c.mem th.promises)
  have ht : t ∈ TermFul.promsOf (promise c j a v w) j := by
    rw [TermFul.promsOf_some hpi.2.1]; exact htm
  have hmt : (promise c j a v w).mem[t]? = some m := by
    rw [hpi.1]; exact hmm
  have hsc := fun c1 h1 h2 => (hrun X S0 hS_S0 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => (hrun X S0 hS_S0 c1 h1 h2).2
  obtain ⟨m', hm', c1, c2, th1, h1, h2, hc2, hth1, -, ht1, -, hsw⟩ :=
    certified_fulfilC X.cert (pwf_of_inv h0.toF.toInvAt) ht
  rw [hmt] at hm'
  cases hm'
  have hc1 : Certified p k arch c1 j := certified_back (.thread h2 (.refl _)) hc2
  obtain ⟨th1', E1, hth1', hx1, ⟨ρ, η, cx, rfl, hE, hT, htv, hi, -⟩, hmi1, -, -, hfb1, -, -, -, hIL1, hIH1, hPV1, hPO1⟩ :=
    solo_typedXFP (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin h0 (TermMain.tidAt_cutP X.inv j S0) h1 hc1 (fun l => X.inv.rle l) (hbr X S0) (hbp X) (TermTyped.witP_run X.hth hm.2.2.1 (TermCert.winInv_prom (TermCert.winInv_refl X.hth)))
  rw [hth1] at hth1'
  cases hth1'
  have hscope := hsc c1 h1 hc1 th1 hth1 (TermTyped.not_spawnT_of_steps hth1 h2) ρ η cx hE hT htv hi
  -- the global count at `m.loc.label` dominates the certificate's (`RunAgree.ini`)
  have hag := hagree X S0 c1 th1 (CE η) h1 hc1 hth1 hx1 hmi1 (by
    have e : (promise c j a v w).mem.size = c.mem.size + 1 := by rw [hpi.1, Array.size_push]
    rw [e] at hfb1; exact hfb1) hIL1 hIH1 hPV1 hPO1
  obtain ⟨hcl0, hgle⟩ := plantIni_le (hV0 := hV0) hP hrun X hcl hsh hag hPS hSub hSig
  rcases SWIni hE hT htv hi hmi1 (TermTyped.scopeD_SW hscope hsw) hsw with ⟨c', hc', hI⟩ | ⟨x, bb, i, v', e, hterm⟩
  · have hc'' : η.sto m.loc.label = some c' := hc'
    have hE1 : η.sto m.loc.label = some cl := hx1.2.2.2.2.1 _ _ hcl0
    rw [hE1] at hc''
    cases hc''
    exact fun N e us h1 h2 => Nat.lt_of_lt_of_le (hI N e us h1 h2) (Nat.mul_le_mul_right _ hgle)
  · exact hbuf X t m htm hmm c1 th1 x bb i v' e h1 hc1 hth1 hterm ht1 cl hcl hsh


/-- **PromNewOKF, InitR half**. -/
theorem promNewIni_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0) (hbr : BufInitPubFR p k arch Sp Init MintOK c0) (hbuf : BufInitIniF p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (cl : Cell) (hcl : Eg.sto a.label = some cl)
    (hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared a.label) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    InitR (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl a.label a.offset :=
  promIniGen (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) (m := ⟨a, v, w⟩) hP hrun hagree hbp hbr hbuf X (List.mem_append_right _ (List.mem_singleton_self _))
    Array.getElem?_push_size cl hcl hsh
end

#print axioms promNewIni_of

/-! ## PromNewOKF, WordOK half (one-word segments; multi-word: the W2 part) -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (named; W2) `WordOK` of a promise (old or new) at a label shared after a promise step, at multi-word segments (part of the one W2 gap,
with `PlantInhWF`). -/
def PromWordWF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ t m, t ∈ th.promises ++ [c.mem.size] → (c.mem.push ⟨a, v, w⟩)[t]? = some m →
    ∀ cl, Eg.sto m.loc.label = some cl →
      (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared m.loc.label →
      InitR (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl m.loc.label m.loc.offset →
      (m.loc.label = a.label ∨ PlantL c Eg j th a v w m.loc.label) → m.view < c.mem.size →
      ∀ b S us, SegOf cl.ty b S → accs S = some us → nWords us ≠ 1 → b ≤ m.loc.offset → m.loc.offset < b + nWords us →
        WordOK (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl.ty m.loc.offset (mw m)

/-- (named; W2, the newly planted part of `PromWordWF`) `PromWordWF` at a multi-word slot of a
planted label that the plant newly initialises (not initialised at `Eg.ini`).  Proved:
`W2New.promWordNew_of` (the other slots: `W2Prom.promWordW_of`). -/
def PromWordNewF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ t m, t ∈ th.promises ++ [c.mem.size] → (c.mem.push ⟨a, v, w⟩)[t]? = some m →
    ∀ cl, Eg.sto m.loc.label = some cl → PlantL c Eg j th a v w m.loc.label → m.view < c.mem.size →
      InitR (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl m.loc.label m.loc.offset →
      ∀ b S us, SegOf cl.ty b S → accs S = some us → nWords us ≠ 1 → b ≤ m.loc.offset → m.loc.offset < b + nWords us →
        ¬ IniSegN (Eg.ini m.loc.label) cl b →
        WordOK (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl.ty m.loc.offset (mw m)

/-- **WordOK of a promise at a label shared after a promise step** (the new promise, or an old one
of the promiser at the promised label or a planted label). -/
theorem promWordGen (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0) (hbr : BufInitPubFR p k arch Sp Init MintOK c0)
    (hW2 : PromWordWF p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {t : Ts} {m : Msg} (htm : t ∈ th.promises ++ [c.mem.size]) (hmm : (c.mem.push ⟨a, v, w⟩)[t]? = some m)
    (hlab : m.loc.label = a.label ∨ PlantL c Eg j th a v w m.loc.label) (hpv : m.view < c.mem.size)
    (cl : Cell) (hcl : Eg.sto m.loc.label = some cl)
    (hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared m.loc.label)
    (hI : InitR (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl m.loc.label m.loc.offset) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    WordOK (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl.ty m.loc.offset (mw m) := by
  obtain ⟨S0, hS_S0⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hS_S0
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hSC : StoClo (Cut Eg j S0) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  obtain ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, -, -, -, hIH0⟩ := InvAtXF_of (p := p) (k := k) (arch := arch)
    hpi.2.1 hTE (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm) hSC (by rw [gOf_promise]; exact X.inv.bf)
    (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh _ _ _ X.hth))
    (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
      (Nat.sub_le_sub_right (by rw [hpi.1]; show c.mem.size ≤ (c.mem.push _).size; rw [Array.size_push]; exact Nat.le_succ _) 1))
  have hX : InvAtX p k arch j (Cut Eg j S0) _ _ (promise c j a v w) :=
    ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, fun _ _ _ h => h.elim, hIH0⟩
  have ht : t ∈ TermFul.promsOf (promise c j a v w) j := by
    rw [TermFul.promsOf_some hpi.2.1]; exact htm
  have hmt : (promise c j a v w).mem[t]? = some m := by
    rw [hpi.1]; exact hmm
  have hsc := fun c1 h1 h2 => (hrun X S0 hS_S0 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => (hrun X S0 hS_S0 c1 h1 h2).2
  have hXH := TermIni.InvAtXHP_promOf (k := k) (arch := arch) (a0 := a) (vB := v) (w := w) X.hth hTE hm hSC X.inv.bf
    (fun l => X.inv.rle l) (X.inv.riniCoh _ _ _ X.hth)
    (fun l cl f hs hp => X.inv.frlt l cl f (cutSto_sub hs) hp) (IniZK Eg Tot HP j) (TermTyped.WitP c.mem th.promises)
  obtain ⟨-, c2, th2, E2, h2, hc2, hth2, hx2, -, hm2, hw2, hfb2H, hB2, hIL2, hIH2, hPV2, hPO2⟩ :=
    TermIni.certified_promNotUndefXHP (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hXH (TermMain.tidAt_cutP X.inv j S0) X.cert (fun l => X.inv.rle l) (hbr X S0) ht hmt (hbp X) (TermTyped.witP_run X.hth hm.2.2.1 (TermCert.winInv_prom (TermCert.winInv_refl X.hth)))
  have hfb2 : FrBound (Cut Eg j S0) (promise c j a v w).mem.size th.vs.vWr E2 := by
    have e : (promise c j a v w).mem.size = c.mem.size + 1 := by rw [hpi.1, Array.size_push]
    rw [e]; exact hfb2H
  have hLc0 : ∀ l1, PlantL c Eg j th a v w l1 →
      ∃ cl1, cutSto Eg j l1 = some cl1 ∧ cl1.owner = some j ∧ Eg.pfr l1 = none := fun l1 h => by
    obtain ⟨-, -, t, -, m, -, -, -, a', g, -, hal, cl1, hc1, ho1, hn1⟩ := h
    subst hal
    exact ⟨cl1, hc1, ho1, hn1⟩
  -- the cell in the promiser's cut, and its type facts
  obtain ⟨hcl0, hnT, hrT⟩ : (Cut Eg j S0).sto m.loc.label = some cl ∧ Ty.noOwnIn [] cl.ty = true ∧
      rgnFree cl.ty = true := by
    rcases hsh with ⟨f, hf⟩
    by_cases hL : PlantL c Eg j th a v w m.loc.label
    · obtain ⟨l', -, hR⟩ := id hL
      obtain ⟨cl2, hc2, ho2, -, -, -, -, h4, h5⟩ := plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
      rw [hcl] at hc2; cases hc2
      exact ⟨cutSto_own hcl ho2, h4, h5⟩
    · have hn := plantOf_none X.hth hL
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr m.loc.label = some f := hf
      simp only [plantG, hn] at h
      have hc0 : (Cut Eg j S0).sto m.loc.label = some cl := cutSto_shared hcl ⟨f, h⟩
      obtain ⟨-, -, -, h4, h5⟩ := hm.2.2.2.2.2.2.2.2.1.2.2.1 m.loc.label cl f hc0 h
      exact ⟨hc0, h4, h5⟩
  obtain ⟨b, S, ws, o', w0, hseg, ⟨hv, hshp⟩, hw0, hle, hbo⟩ := hw2 cl hcl0
  obtain ⟨us, hus⟩ : ∃ us, accs S = some us := by
    rcases hseg with ⟨-, rfl, hA⟩ | ⟨N, us, jj, -, hus, -, -⟩
    · exact Option.ne_none_iff_exists'.1 hA
    · exact ⟨us, hus⟩
  have hlen : ws.length = nWords us := hshp us hus
  have hnS := noOwn_seg hseg hnT
  have hrS := rgnFree_seg hseg hrT
  have ho'lt : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
  by_cases h1 : nWords us = 1
  rotate_left
  · have hbo' : b + o' = m.loc.offset := hbo
    exact hW2 X t m htm hmm cl hcl hsh hI hlab hpv b S us hseg hus h1 (by omega) (by rw [← hbo']; exact Nat.add_lt_add_left (hlen ▸ ho'lt) b)
  obtain ⟨rfl, rfl⟩ : o' = 0 ∧ ws = [w0] := by
    match ws, hlen, hw0 with
    | [x], _, hw0 =>
      cases o' with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hw0; exact ⟨rfl, by rw [hw0]⟩
      | succ n => simp at hw0
    | [], hl, _ => rw [h1] at hl; cases hl
    | _ :: _ :: _, hl, _ => rw [h1] at hl; simp at hl
  have hR := TermIni.RunAgree_ofW (hagree X S0 c2 th2 E2 h2 hc2 hth2 hx2 hm2 hfb2H hIL2 hIH2 hPV2 hPO2) (TermIni.runAgree_pfrL hB2 (MemInv_promLt hm) (fun l c h => hx2.2.2.2.2.1 l c h)
      (fun l1 h => by obtain ⟨cl1, h1, -, -⟩ := hLc0 l1 h; exact ⟨cl1, h1⟩)
      (fun l1 h => by obtain ⟨-, -, -, hn1⟩ := hLc0 l1 h; exact hn1))
  have hbi := hm2.2.2.2.2.2.2.2.2.2.1
  have hLc := hLc0
  have hV1 : ValOf (plantE (Cut Eg j S0) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)) S [w0] := by
    refine ValOf_monoK (G := PlantG (Cut Eg j S0) (PlantL c Eg j th a v w)) hnS hrS hus (by rw [h1]; rfl)
      hx2.2.2.1 hx2.2.2.2.1 (fun l c0 hG hc0 => ?_) (fun l hG => ?_) (fun l f hG hf => ?_) (fun l B hG hB => ?_)
      hR.pay ?_ hv
    · show (Cut Eg j S0).sto l = some c0
      rcases hG with ⟨c1, f, h1', -⟩ | hLa | ⟨B, hB⟩
      · rw [hx2.2.2.2.2.1 l c1 h1'] at hc0; rw [h1', hc0]
      · obtain ⟨c1, h1', -⟩ := hLc l hLa
        have h1'' : (Cut Eg j S0).sto l = some c1 := h1'
        rw [hx2.2.2.2.2.1 l c1 h1''] at hc0; rw [h1'', hc0]
      · have := (hbi.2.2 l B (hx2.2.2.2.2.2.2.2.2.1 l B hB)).1
        rw [hc0] at this; cases this
    · rcases hG with hG | hLa | ⟨B, hB⟩
      · exact hR.ini l (.inl hG)
      · exact hR.ini l (.inr hLa)
      · rw [(hbi.2.2 l B (hx2.2.2.2.2.2.2.2.2.1 l B hB)).2.1]; exact Nat.zero_le _
    · rcases hG with ⟨c1, f0, h1', hf0⟩ | hLa | hB
      · have hnL : ¬ PlantL c Eg j th a v w l := fun hLa => by
          obtain ⟨-, -, -, hn1⟩ := hLc l hLa
          have : (Cut Eg j S0).pfr l = none := hn1
          rw [this] at hf0; cases hf0
        rw [hx2.2.2.2.2.2.2.1 l f0 hf0] at hf
        cases hf
        exact ⟨_, by rw [plantE_pfr_ne hnL]; exact hf0, Nat.le_refl _⟩
      · exact hR.pfr l f (.inl hLa) hf
      · exact hR.pfr l f (.inr hB) hf
    · show (Cut Eg j S0).box l = some B
      rcases hG with ⟨c1, f, h1', -⟩ | hLa | ⟨B0, hB0⟩
      · have := (hbi.2.2 l B hB).1
        rw [hx2.2.2.2.2.1 l c1 h1'] at this; cases this
      · obtain ⟨c1, h1', -⟩ := hLc l hLa
        have := (hbi.2.2 l B hB).1
        rw [hx2.2.2.2.2.1 l c1 h1'] at this; cases this
      · rw [hx2.2.2.2.2.2.2.2.2.1 l B0 hB0] at hB; rw [hB0, hB]
    · intro w1 hw1 a' g hv'
      rw [List.mem_singleton] at hw1
      subst hw1
      have hJ := noJunk_valOf hv hnS hrS hus (by rw [h1]; rfl) w1 (List.mem_singleton_self _) a' g hv'
      have hvm : w1.view ≤ m.view := hle.2 a' g hv'
      have hmv : m.val = .loc a' g := by rw [← hv']; exact hle.1.symm
      have hfb2' : FrBound (Cut Eg j S0) (c.mem.size + 1) th.vs.vWr E2 := by
        have e : (promise c j a v w).mem.size = c.mem.size + 1 := by rw [hpi.1, Array.size_push]
        rw [e] at hfb2; exact hfb2
      rcases FrBound_inspM hfb2' hJ (Nat.lt_of_le_of_lt hvm hpv) with ⟨c1, hc1⟩ | ⟨B, hB⟩
      · rcases hpf : (Cut Eg j S0).pfr a'.label with _ | f
        · -- an own private unplanted cell named by the new promise: a plant edge from `m.loc.label`
          have ho1 : c1.owner = some j := by
            rcases (cutSto_some.1 hc1).2 with h | ⟨f2, hf2⟩
            · exact h
            · have : Eg.pfr a'.label = none := hpf
              rw [this] at hf2; cases hf2
          have hroot : ClR (PlantR (cutP Eg j) (c.mem.push ⟨a, v, w⟩) (th.promises ++ [c.mem.size])) a.label
              m.loc.label := by
            rcases hlab with h | ⟨l', h1', hR'⟩
            · rw [h]; exact ClR.base
            · exact ClR.step h1' hR'
          exact .inr (.inl ⟨m.loc.label, hroot, ⟨t, htm, m, hmm, rfl, ⟨cl, hcl0, hnT, hrT⟩, a', g, hmv, rfl, c1, hc1,
            ho1, hpf⟩⟩)
        · exact .inl ⟨c1, f, hc1, hpf⟩
      · exact .inr (.inr ⟨B, hB⟩)
  have hV2 := ValOf_transferS (InclS_cut_pub (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j S0)
    (noOR_of S [] hnS hrS) (ValOf_transferS (inclS_plantE X S0 j S0) (noOR_of S [] hnS hrS) hV1)
  exact ⟨b, S, [w0], 0, w0, hseg, ⟨hV2, hshp⟩, rfl, hle, hbo⟩


/-- **PromNewOKF, WordOK half.** -/
theorem promNewWord_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0) (hbr : BufInitPubFR p k arch Sp Init MintOK c0)
    (hW2 : PromWordWF p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (cl : Cell) (hcl : Eg.sto a.label = some cl)
    (hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared a.label)
    (hI : InitR (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl a.label a.offset) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    WordOK (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl.ty a.offset (mw ⟨a, v, w⟩) :=
  promWordGen (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) (m := ⟨a, v, w⟩) hP hrun hagree hbp hbr hW2 X (List.mem_append_right _ (List.mem_singleton_self _))
    Array.getElem?_push_size (.inl rfl) X.hw cl hcl hsh hI
end

#print axioms promNewWord_of

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **P4b residual `PromNewOKF`** for `plantOf`/`plantN`. -/
theorem promNewOK_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0) (hbr : BufInitPubFR p k arch Sp Init MintOK c0) (hbuf : BufInitIniF p k arch Sp Init MintOK c0)
    (hW2 : PromWordWF p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PromNewOKF p k arch Sp Init MintOK c0 plantOf plantN :=
  fun X cl hcl hsh =>
    have hI := promNewIni_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun hagree hbp hbr hbuf X cl hcl hsh
    ⟨hI, promNewWord_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun hagree hbp hbr hW2 X cl hcl hsh hI⟩

end

#print axioms promNewOK_of

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **P4b residual `PlantPromOKF`** for `plantOf`/`plantN`: the promiser's old promises at a
planted label are initialised (planted count) and typed (holders' values). -/
theorem plantPromOK_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0) (hbr : BufInitPubFR p k arch Sp Init MintOK c0) (hbuf : BufInitIniF p k arch Sp Init MintOK c0)
    (hW2 : PromWordWF p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PlantPromOKF p k arch Sp Init MintOK c0 plantOf plantN := by
  intro c Eg Tot HP HS cr db j th a v w X l f hpl t m ht hm hl cl hcl
  have hlt : t < c.mem.size := TermPlant.lt_size_of_some hm
  have hmm : (c.mem.push ⟨a, v, w⟩)[t]? = some m := by
    rw [Array.getElem?_push_lt hlt]; simpa [hlt] using hm
  have htm : t ∈ th.promises ++ [c.mem.size] := List.mem_append_left _ ht
  subst hl
  have hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared m.loc.label :=
    ⟨f, by show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr m.loc.label = some f
           simp only [plantG, hpl]⟩
  have hpv : m.view < c.mem.size := by
    obtain ⟨m', hm', hvl⟩ := promViewLt_run h0 X.run j th t X.hth ht
    rw [hm] at hm'; cases hm'
    exact Nat.lt_trans hvl hlt
  have hI := promIniGen (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun hagree hbp hbr hbuf X htm hmm cl hcl hsh
  exact ⟨hI, promWordGen (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun hagree hbp hbr hW2 X htm hmm (.inr (plantOf_some X.hth hpl).1) hpv cl hcl hsh hI⟩

end

#print axioms plantPromOK_of

/-! ## PubPromOKF (thread step): the stepper's promises at a cell the step newly shares

The certificate from `c'` starts at the stepper's post-step typing `E'` (`TOut`).  The fulfilling
write is typed at `E1 ⊇ E'` (`SWIni`), and `E1`'s count at the cell is at most `E'`'s (`RunAgreeT`,
the thread-step half of the RunAgree field), which is `EgT`'s.  The value is typed at `E2 ⊇ E'`
(`certified_promNotUndefX`) and moved to `E'` by `ValOf_monoK` (published `E'` cells and boxes), then
to `PubE EgT` (`InclS`). -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}

/-- (named run fact; thread-step half of the RunAgree field: = `hIniStab` + the pfr/pay
items) `RunAgree` for the certificate environments of a thread step's successor, from the stepper's
post-step environment, without plant set. -/
def RunAgreeT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ c1 th1 E1, Solo p k arch i c' c1 → Certified p k arch c1 i → c1.ths[i]? = some th1 → Ext E' E1 →
      MemInv (gOf p k arch c1 i) E1 (stOf c1.mem c1.pairs th1) → FrBound E' c'.mem.size r.2.2.vs.vWr E1 →
      TermTyped.IniLoc (IniZTK Eg Tot HP i th) E' E1 →
      TermTyped.IniHeld (TermTyped.WitP c'.mem r.2.2.promises) E' E1 th1.vs.vWr →
      TermK5O.PfrProvO p k arch i (TermTyped.WitP c'.mem r.2.2.promises) E' c' c1 E1 → RunAgree E' E' (fun _ => False) E1

/-- (named run fact; thread-step half of the BufInitIni field: = route R-b `ownSeen` at a published
cell, F2′ P3 at a thread-step plant) A `bufInit` fulfilling one of the stepper's promises at a cell
the step newly shares writes an offset initialised in `EgT`'s count. -/
def BufInitIniT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ l f, Eg.pfr l = none → E'.pfr l = some f → ∀ t m, t ∈ r.2.2.promises → c'.mem[t]? = some m → m.loc.label = l →
    ∀ c1 th1 x bb i' v' e, Solo p k arch i c' c1 → Certified p k arch c1 i → c1.ths[i]? = some th1 →
      th1.term = .let_ x (.bufInit bb i' v') e → t ∈ th1.promises →
      BufInitOn th1 l →
      ∀ cl, Eg.sto l = some cl →
        InitR (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')) cl l m.loc.offset

/-- (named; third conjunct of W2F) `WordOK` of the stepper's promise at a newly shared cell, at
multi-word segments. -/
def PubWordWF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ crS : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) crS (db i) δ →
    (∀ l, TermOwnG0Defs.PubAt th l → ∀ t, crS t = cr i t) →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    ∀ l f, Eg.pfr l = none → E'.pfr l = some f → ∀ t m, t ∈ r.2.2.promises → c'.mem[t]? = some m → m.loc.label = l →
      ∀ cl, Eg.sto l = some cl →
        InitR (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')) cl l m.loc.offset →
        ∀ b S' us, SegOf cl.ty b S' → accs S' = some us → nWords us ≠ 1 →
        b ≤ m.loc.offset → m.loc.offset < b + nWords us →
        WordOK (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')) cl.ty m.loc.offset (mw m)

/-- (named; the PlantedClos fact, explorer-probed) A promise of the stepper at a cell the step newly
shares, whose value names one of the stepper's cells, names a cell with a frontier (it was planted
when that promise was made, `plantOf`'s closure; a promise at a not-yet-allocated cell is
uncertifiable). -/
def PubClosT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ l f, Eg.pfr l = none → E'.pfr l = some f → ∀ t m, t ∈ r.2.2.promises → c'.mem[t]? = some m → m.loc.label = l →
      ∀ (a' : Address) (g : Nat), m.val = .loc a' g → ∀ cl, E'.sto a'.label = some cl → cl.owner = some i →
        ∃ f', E'.pfr a'.label = some f'

end

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}

/-- The stepper's post-step environment sits inside the shared part of `EgT`. -/
theorem inclS_post
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ) :
    InclS E' (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')) := by
  have hF := Z.1
  have hCE : CE η = Cut Eg i S := Y.1
  refine ⟨hF.1.trans (by rw [hCE]; rfl), fun l c1 f hc hf => ?_, fun l => Nat.le_refl _, fun l f hf => hf,
    fun l B hB => ?_, fun l => Nat.le_refl _⟩
  · have hsh : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').Shared l := ⟨f, hf⟩
    rw [PubE_sto hsh]
    by_cases hfr : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
    · simp [EgT, GEnv.withFp, GEnv.post, hfr, hc]
    · have e : E'.sto l = (CE η).sto l := (hF.2.2.1 l).resolve_right (fun h => hfr h.1)
      rw [e, hCE] at hc
      simp [EgT, GEnv.withFp, GEnv.post, hfr, cutSto_sub hc]
  · show (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').box l = some B
    by_cases hfr : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
    · simp [EgT, GEnv.withFp, GEnv.post, hfr, hB]
    · have e : E'.box l = (CE η).box l := (hF.2.2.2.1 l).resolve_right (fun h => hfr h.1)
      rw [e, hCE] at hB
      simp [EgT, GEnv.withFp, GEnv.post, hfr]
      exact hB

/-- A cell of the post-step environment without frontier is the stepper's. -/
theorem post_own_of_nopfr
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {l : AllocLabel} {cl : Cell} (hc : E'.sto l = some cl) (hn : E'.pfr l = none) : cl.owner = some i := by
  have hF := Z.1
  have hCE : CE η = Cut Eg i S := Y.1
  rcases hF.2.2.1 l with e | ⟨-, T, hT, -⟩
  · rw [e, hCE] at hc
    rcases (cutSto_some.1 hc).2 with h | ⟨f, hf⟩
    · exact h
    · exfalso
      rcases hF.2.2.2.2.2.1 l with e2 | ⟨h0, -⟩ | ⟨-, h0, -⟩
      · have h := e2.symm.trans hn
        rw [hCE] at h
        have : Eg.pfr l = none := h
        rw [this] at hf; cases hf
      · have : Eg.pfr l = none := by rw [hCE] at h0; exact h0
        rw [this] at hf; cases hf
      · have : Eg.pfr l = none := by rw [hCE] at h0; exact h0
        rw [this] at hf; cases hf
  · rw [hT] at hc; cases hc
    show some (CE η).tid = some i
    rw [hCE]; rfl

end

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (bufInit rework) A stepper write at a `bufInit` names the `bufInit`'s buffer cell (`BufInitOn`). -/
theorem sw_bufInit_on {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {loc : Address} {val : WeakMem.Val}
    {y : String} {bb ib v : At} {e : Expr} (hterm : th.term = .let_ y (.bufInit bb ib v) e)
    (h : TermFul.SW g mem pairs th loc val) : BufInitOn th loc.label := by
  rcases h with ⟨x', op, e', ht, hw⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, -⟩
  · rw [hterm] at ht
    cases ht
    rcases hw with ⟨pw, b, rel, us, ws, j, w, hU, -, -, hloc, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hop, -⟩
    · obtain ⟨-, t, t1, t2, iws, μ, u, j', a0, μ', n, e'', ψ, hbb, -, -, -, -, ha0, -, -, hb⟩ := hU
      unfold addrOf at ha0
      split at ha0
      · rename_i a1 g1 hv
        simp only [Option.some.injEq] at ha0
        subst ha0; subst hloc; subst hb
        exact ⟨y, bb, ib, v, e, t, pw, a1, g1, hterm, hbb, hv, rfl⟩
      · cases ha0
    · cases hop
  · rw [hterm] at ht; cases ht

/-- The cell a thread step newly shares (`Eg.pfr l = none`, `E'.pfr l = some f`): it is not fresh, and
`cl` (its `Eg` cell) is its cell in `CE η` and in `E'`.  Shared by `pubPromOK_of` and
`W2Pub.pubWordW_of` (copy rule). -/
theorem pubCell_of {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ crS : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) crS (db i) δ)
    {l : AllocLabel} {f} (hn0 : Eg.pfr l = none) (hf : E'.pfr l = some f) {cl} (hcl : Eg.sto l = some cl) :
    ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l ∧ (CE η).sto l = some cl ∧ E'.sto l = some cl := by
  have hF := Z.1
  have hCE : CE η = Cut Eg i S := Y.1
  have hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun ⟨jj, hjj, _, hlj⟩ => by
    have hl' : l = freshLabel c.lbase c.n i jj := hlj
    have := (X.inv.fresh i th X.hth jj hjj).1
    rw [← hl', hcl] at this; cases this
  have hCl : (CE η).sto l = some cl := by
    rw [hCE]
    rcases hF.2.2.2.2.2.1 l with e2 | ⟨-, -, -, -, -, ⟨cc, hcc, hoc⟩, -⟩ | ⟨hfr, -⟩
    · exfalso
      have h := e2.symm.trans hf
      rw [hCE] at h
      have : Eg.pfr l = some f := h
      rw [hn0] at this; cases this
    · rw [hCE] at hcc
      rw [cutSto_sub hcc] at hcl; cases hcl; exact hcc
    · exact absurd hfr hnf
  have hcl' : E'.sto l = some cl := by
    rw [(hF.2.2.1 l).resolve_right (fun h => hnf h.1)]; exact hCl
  exact ⟨hnf, hCl, hcl'⟩

/-- **T16b/T16d residual `PubPromOKF`**: the stepper's promises at a cell the step newly shares
are initialised and typed in `PubE EgT`. -/
theorem pubPromOK_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrunT : CertRunT p k arch Sp Init MintOK c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hagree : RunAgreeT p k arch Sp Init MintOK c0) (hbp : BufInitPubT p k arch Sp Init MintOK c0)
    (hbtr : BufInitPubTR p k arch Sp Init MintOK c0) (hbuf : BufInitIniT p k arch Sp Init MintOK c0)
    (hclos : PubClosT p k arch Sp Init MintOK c0) (hW2 : PubWordWF p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PubPromOKF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS X Y Z hPub hPfrP hS l f hn0 hf t m ht hm hl cl hcl
  have hF := Z.1
  have hRE := Z.2.1
  have hmE := Z.2.2.1
  have hAP := TermXFO.anchPost (hV0 := hV0) X Y.1 (Z.toC Rf Rs (HP i + HS) (cr i) (db i)) hS hPfrP (hrunT X S hS).1
  have hCE : CE η = Cut Eg i S := Y.1
  have hg : gOf p k arch c' i = gOf p k arch c i := TermTyped.gOf_thread X.hc'
  have hSC0 : StoClo (CE η) := by
    rw [hCE]; exact fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have hst : stOf c'.mem c'.pairs r.2.2 = stOf r.1 r.2.1 r.2.2 := by rw [X.e1, X.e2]
  have h0X := TermXFO.InvAtXFO_ofA (p := p) (k := k) (arch := arch) (Ea := Cut Eg i S) X.e3 hRE.thInvE (by rw [hg, hst]; exact hmE)
    (StoClo_EFoot hF hSC0) (by rw [hg]; exact X.inv.bf) (by rw [hst]; exact hAP.1) (.inr hAP.2) (IniZTK Eg Tot HP i th) (TermTyped.WitP c'.mem r.2.2.promises)
  have hrlE : ∀ l, E'.rini l ≤ E'.ini l := hF.2.2.2.2.2.2.2.2.2.2.1 (fun l => by rw [hCE]; exact X.inv.rle l)
  have hHrT := TermTyped.witP_run (p := p) (k := k) (arch := arch) X.e3
    (fun t ht => by rw [X.e1]; exact hmE.2.2.1 t ht) (TermCert.winInv_refl X.e3)
  have hsc := fun c1 h1 h2 => ((hrunT X S hS).2 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => ((hrunT X S hS).2 c1 h1 h2).2
  have ht' : t ∈ TermFul.promsOf c' i := by rw [TermFul.promsOf_some X.e3]; exact ht
  -- the newly shared cell in `E'`
  obtain ⟨hnf, hCl, hcl'⟩ := pubCell_of X Y Z hn0 hf hcl
  -- the step publishes `l`, so the stepper's credits are the thread's
  have hPl : TermOwnG0Defs.PubAt th l := hPfrP l (by rw [hCl]; exact Option.some_ne_none _)
    (by rw [hf, hCE]; show some f ≠ Eg.pfr l; rw [hn0]; exact Option.some_ne_none _)
  have hcrS : crS = cr i := funext (hPub l hPl)
  subst hcrS
  have ZC := Z.toC Rf Rs (HP i + HS) (cr i) (db i)
  have hlt : t < c'.mem.size := TermPlant.lt_size_of_some hm
  have hI : InitR (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')) cl l m.loc.offset := by
    obtain ⟨m', hm'', c1, c2, th1, h1, h2, hc2, hth1, -, ht1, -, hsw⟩ :=
      certified_fulfilC X.cert (pwf_of_inv h0X.toF.toInvAt) ht'
    rw [hm] at hm''
    cases hm''
    have hc1 : Certified p k arch c1 i := certified_back (.thread h2 (.refl _)) hc2
    obtain ⟨th1', E1, hth1', hx1, ⟨ρ1, η1, cx1, rfl, hE1, hT1, htv1, hi1, -⟩, hmi1, -, -, hfb1, -, -, -, hIL1, hIH1, hPO1⟩ :=
      TermXFO.solo_typedXFO (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin h0X (TermTyped.tidAt_mono hAP.2 (TermTyped.tidAt_thread X.hc' (TermMain.tidAt_cut X.inv i S))) h1 hc1 hrlE (hbtr X Y Z hPfrP)
        (hbp X) hHrT
    rw [hth1] at hth1'
    cases hth1'
    have hscope := hsc c1 h1 hc1 th1 hth1 (TermTyped.not_spawnT_of_steps hth1 h2) ρ1 η1 cx1 hE1 hT1 htv1 hi1
    have hag := hagree X Y Z hPfrP c1 th1 (CE η1) h1 hc1 hth1 hx1 hmi1 hfb1 hIL1 hIH1 hPO1
    have hgle : (CE η1).ini l ≤ (PubE (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')).ini l :=
      hag.ini l (.inl ⟨cl, f, hcl', hf⟩)
    rcases SWIni hE1 hT1 htv1 hi1 hmi1 (TermTyped.scopeD_SW hscope hsw) hsw with ⟨c'', hc'', hI⟩ | ⟨x, bb, i', v', e, hterm⟩
    · have hc3 : η1.sto m.loc.label = some c'' := hc''
      have hE1 : η1.sto l = some cl := hx1.2.2.2.2.1 _ _ hcl'
      rw [hl, hE1] at hc3
      cases hc3
      rw [hl] at hI
      exact fun N e us h1 h2 => Nat.lt_of_lt_of_le (hI N e us h1 h2) (Nat.mul_le_mul_right _ hgle)
    · rw [← hl] at hcl
      have := hbuf X Y ZC hPfrP l f hn0 hf t m ht hm hl c1 th1 x bb i' v' e h1 hc1 hth1 hterm ht1
        (by rw [← hl]; exact sw_bufInit_on hterm hsw) cl (by rw [← hl]; exact hcl)
      rw [← hl] at this ⊢; exact this
  refine ⟨hI, ?_⟩
  · -- WordOK
    obtain ⟨-, c2, th2, E2, h2, hc2, hth2, hx2, -, hm2, hw2, hfb2, hIL2, hIH2, hPO2⟩ :=
      TermXFO.certified_promNotUndefXO (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin h0X (TermTyped.tidAt_mono hAP.2 (TermTyped.tidAt_thread X.hc' (TermMain.tidAt_cut X.inv i S))) X.cert hrlE
        (hbtr X Y Z hPfrP) ht' hm (hbp X) hHrT
    obtain ⟨-, -, -, hnT, hrT⟩ := hmE.2.2.2.2.2.2.2.2.1.2.2.1 l cl f hcl' hf
    obtain ⟨b, S', ws, o', w0, hseg, ⟨hv, hshp⟩, hw0, hle, hbo⟩ := hw2 cl (by rw [hl]; exact hcl')
    obtain ⟨us, hus⟩ : ∃ us, accs S' = some us := by
      rcases hseg with ⟨-, rfl, hA⟩ | ⟨N, us, jj, -, hus, -, -⟩
      · exact Option.ne_none_iff_exists'.1 hA
      · exact ⟨us, hus⟩
    have hlen : ws.length = nWords us := hshp us hus
    have hnS := noOwn_seg hseg hnT
    have hrS := rgnFree_seg hseg hrT
    have ho'lt : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
    have hbo' : b + o' = m.loc.offset := hbo
    by_cases h1 : nWords us = 1
    rotate_left
    · exact hW2 X Y Z (fun _ _ _ => rfl) hPfrP hS l f hn0 hf t m ht hm hl cl hcl hI b S' us hseg hus h1 (hbo' ▸ Nat.le_add_right b o')
        (by rw [← hbo']; exact Nat.add_lt_add_left (hlen ▸ ho'lt) b)
    obtain ⟨rfl, rfl⟩ : o' = 0 ∧ ws = [w0] := by
      match ws, hlen, hw0 with
      | [x], _, hw0 =>
        cases o' with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hw0; exact ⟨rfl, by rw [hw0]⟩
        | succ n => simp at hw0
      | [], hl, _ => rw [h1] at hl; cases hl
      | _ :: _ :: _, hl, _ => rw [h1] at hl; simp at hl
    have hR := hagree X Y Z hPfrP c2 th2 E2 h2 hc2 hth2 hx2 hm2 hfb2 hIL2 hIH2 hPO2
    have hbi := hm2.2.2.2.2.2.2.2.2.2.1
    have hpvl : m.view < t := by
      obtain ⟨m', hm', hvl⟩ := promViewLt_step (promViewLt_run h0 X.run) (Step.thread i X.hc' X.cert) i r.2.2 t X.e3 ht
      rw [hm] at hm'; cases hm'; exact hvl
    obtain ⟨n, hn⟩ : ∃ n, c'.mem.size = n + 1 :=
      ⟨c'.mem.size - 1, (Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)).symm⟩
    have hfb2' : FrBound E' (n + 1) r.2.2.vs.vWr E2 := by rw [← hn]; exact hfb2
    have hV1 : ValOf E' S' [w0] := by
      refine ValOf_monoK (G := PlantG E' (fun _ => False)) hnS hrS hus (by rw [h1]; rfl)
        hx2.2.2.1 hx2.2.2.2.1 (fun l2 c0 hG hc0 => ?_) (fun l2 hG => ?_) (fun l2 f2 hG hf2 => ?_)
        (fun l2 B hG hB => ?_) hR.pay ?_ hv
      · rcases hG with ⟨c1, f1, h1', -⟩ | hF0 | ⟨B, hB⟩
        · rw [hx2.2.2.2.2.1 l2 c1 h1'] at hc0; rw [h1', hc0]
        · exact hF0.elim
        · have := (hbi.2.2 l2 B (hx2.2.2.2.2.2.2.2.2.1 l2 B hB)).1
          rw [hc0] at this; cases this
      · rcases hG with hG | hF0 | ⟨B, hB⟩
        · exact hR.ini l2 (.inl hG)
        · exact hF0.elim
        · rw [(hbi.2.2 l2 B (hx2.2.2.2.2.2.2.2.2.1 l2 B hB)).2.1]; exact Nat.zero_le _
      · rcases hG with ⟨c1, f0, h1', hf0⟩ | hF0 | hB
        · rw [hx2.2.2.2.2.2.2.1 l2 f0 hf0] at hf2
          cases hf2
          exact ⟨_, hf0, Nat.le_refl _⟩
        · exact hF0.elim
        · exact hR.pfr l2 f2 (.inr hB) hf2
      · rcases hG with ⟨c1, f1, h1', -⟩ | hF0 | ⟨B0, hB0⟩
        · have := (hbi.2.2 l2 B hB).1
          rw [hx2.2.2.2.2.1 l2 c1 h1'] at this; cases this
        · exact hF0.elim
        · rw [hx2.2.2.2.2.2.2.2.2.1 l2 B0 hB0] at hB; rw [hB0, hB]
      · intro w1 hw1 a' g hv'
        rw [List.mem_singleton] at hw1
        subst hw1
        have hJ := noJunk_valOf hv hnS hrS hus (by rw [h1]; rfl) w1 (List.mem_singleton_self _) a' g hv'
        have hvm : w1.view ≤ m.view := hle.2 a' g hv'
        have hmv : m.val = .loc a' g := by rw [← hv']; exact hle.1.symm
        rcases FrBound_inspM hfb2' hJ (Nat.lt_of_le_of_lt hvm (Nat.lt_of_lt_of_le hpvl (Nat.le_of_lt_succ (show t < n + 1 by rw [← hn]; exact hlt)))) with ⟨c1, hc1⟩ | ⟨B, hB⟩
        · rcases hpf : E'.pfr a'.label with _ | f1
          · exfalso
            have ho1 := post_own_of_nopfr Y ZC hc1 hpf
            obtain ⟨f', hf'⟩ := hclos X Y ZC hS hPfrP l f hn0 hf t m ht hm hl a' g hmv c1 hc1 ho1
            rw [hpf] at hf'; cases hf'
          · exact .inl ⟨c1, f1, hc1, hpf⟩
        · exact .inr (.inr ⟨B, hB⟩)
    have hV2 := ValOf_transferS (inclS_post (c' := c') Y ZC) (noOR_of S' [] hnS hrS) hV1
    exact ⟨b, S', [w0], 0, w0, hseg, ⟨hV2, hshp⟩, rfl, hle, hbo⟩

end

#print axioms pubPromOK_of
#print axioms sw_bufInit_on
#print axioms promIniGen
#print axioms promWordGen
#print axioms inclS_plantE
#print axioms inclS_post

/-! ## The named facts, one per field (promise-step and thread-step conjuncts)

These are the replacing fields of `TermMain.ObligationsF`, the instantiation of `Obligations` at
`plantOf`/`plantN`. -/

/-- (named run fact) `RunAgree` along the certificates of a promise step and of a thread step. -/
def RunAgreeFT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  RunAgreeF p k arch Sp Init MintOK c0 ∧ RunAgreeT p k arch Sp Init MintOK c0

/-- (named) a fulfilling `bufInit` writes an initialised offset (promise step: planted cells; thread
step: newly shared cells). -/
def BufInitIniFT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  BufInitIniF p k arch Sp Init MintOK c0 ∧ BufInitIniT p k arch Sp Init MintOK c0

/-- (named, PlantedClos) closure of a promise's location value at a thread step (the promise-step
half is proved: a plant edge carries its source cell's type facts). -/
def PlantClosFT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  PubClosT p k arch Sp Init MintOK c0

end TermPlantF
