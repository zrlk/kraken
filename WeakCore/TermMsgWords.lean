import WeakCore.TermPromAlloc
import WeakCore.TermCohLe

/-! # TermMsgWords: `MsgWordsG` (every message lies within its cell's words)

`SysInvN.msgWords`: every message in memory at a label with a cell lies at an offset within the
cell's words (`InWords`).  Kept by a thread step (`msgWords_thread`: old messages by the invariant,
or, at a label the step allocates, by the owner's `MemOKP` at `E'` (a former promise of the stepper,
fulfilled in the step, `promAlloc_loc`, not `undef`, `promNU`); new messages at a fresh label by
`NewAtT`, elsewhere by `tstep_newPos`) and by a promise step (`msgWords_prom`: the promised address
is in a one-word unit of its cell, `promWords_of`).  `msgInCell_of`: a message at an own cell of
a thread lies in the cell (`InCell`, at the owner's `CellOK` words).
-/

namespace TermMsgWords
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermMain TermInterf TermPlantF TermTyped TermPromClos TermStepper TermNoHold TermPromAlloc
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- A word OK for a cell of type `T` at offset `o` lies within the cell's words. -/
theorem wordOK_inWords {η : TEnv} {T : Ty} {o : Nat} {w : Word} (h : WordOK η T o w) : InWords T o := by
  obtain ⟨b, S, ws, o', w0, hseg, hv, hw0, -, hb⟩ := h
  have hlt : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
  rcases hseg with ⟨rfl, rfl, hT⟩ | ⟨N, us, j, rfl, hus, hj, rfl⟩
  · refine ⟨fun L hL => ?_, fun N e us hT' _ => ?_⟩
    · have := hv.2 L hL
      omega
    · subst hT'
      exact absurd (by simp [accs]) hT
  · refine ⟨fun L hL => by simp [accs] at hL, fun N' e us' hT hus' => ?_⟩
    simp only [Ty.array.injEq, Idx.lit.injEq] at hT
    obtain ⟨rfl, rfl⟩ := hT
    rw [hus] at hus'
    cases hus'
    have hl := hv.2 us hus
    have h2 : (j + 1) * nWords us ≤ N * nWords us := Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at h2
    omega

/-- A word of a unit of a component of a cell of type `T` lies within the cell's words. -/
theorem role_inWords {T U : Ty} {o j : Nat} {us : List Acc} (h : AtOff T o U) (hU : accs U = some us)
    (hj : j < nWords us) : InWords T (o + j) := by
  refine ⟨fun L hL => ?_, fun N e L hT hL => ?_⟩
  · have := AtOff_bound h hL hU
    omega
  · subst hT
    rcases AtOff_arr_elem h rfl with hT | ⟨us', jj, o', hus', hjj, ho, h'⟩
    · rw [hT] at hU; simp [accs] at hU
    · rw [hL] at hus'
      cases hus'
      have h1 := AtOff_bound h' hL hU
      have h2 : (jj + 1) * nWords L ≤ N * nWords L := Nat.mul_le_mul_right _ hjj
      rw [Nat.succ_mul] at h2
      omega

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`MsgWordsG` after a thread step.**  An old message at an old label: the invariant.  An old
message at a label the step allocates is a promise of the stepper (`fresh`), fulfilled in the step
(`promAlloc_loc`), not `undef` (`promNU`): `MemOKP` at `E'`.  A new message at a label the step
allocates: `NewAtT`; elsewhere, `tstep_newPos` at the stepper's own typing (a frame-only step
appends nothing, `frame_keep`). -/
theorem msgWords_thread (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : TermPlantF.CertRunT p k arch Sp Init MintOK c0)
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    (h : MsgWordsG Eg c) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    MsgWordsG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' := by
  intro t m cl hm hsto
  have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
    rw [← Y.1]; exact Z.1
  have hmt : r.1[t]? = some m := by rw [← X.e1]; exact hm
  by_cases hlt : t < c.mem.size
  · have hm0 : c.mem[t]? = some m := by rw [← tctx_pre X t hlt]; exact hm
    by_cases hF : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label
    · obtain ⟨j0, hj0, hj1, hl0⟩ := hF
      have htth : t ∈ th.promises := (X.inv.fresh i th X.hth j0 hj0).2.2.2.2 t m hm0 hl0
      have hnp : t ∉ r.2.2.promises := fun ht =>
        promAlloc_loc (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X Y Z hS hPfr ⟨j0, hj0, hj1, hl0⟩ ht hm rfl
      have hnu : m.val ≠ .undef := X.inv.promNU i th t m X.hth htth hm0
      have hsto' : E'.sto m.loc.label = some cl := by
        have e := post_sto_fresh (Eg := Eg) (E' := E') ⟨j0, hj0, hj1, hl0⟩
        rw [← e]; exact hsto
      rcases Z.2.2.1.1.1 t m cl hnp hmt hsto' with hu | hw
      · exact absurd hu hnu
      · exact wordOK_inWords hw
    · have hsto' : Eg.sto m.loc.label = some cl := by
        have e := post_sto_old (Eg := Eg) (E' := E') hF
        rw [← e]; exact hsto
      exact h t m cl hm0 hsto'
  · have hge : c.mem.size ≤ t := Nat.le_of_not_lt hlt
    by_cases hF : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label
    · have hsto' : E'.sto m.loc.label = some cl := by
        have e := post_sto_fresh (Eg := Eg) (E' := E') hF
        rw [← e]; exact hsto
      rcases hF0.2.2.1 m.loc.label with e | ⟨-, T, hT, -, -, hN⟩
      · rw [e] at hsto'
        have h1 : Eg.sto m.loc.label = some cl := cutSto_sub (i := i) hsto'
        rw [(X.inv.gfresh X.hth r.2.2.nalloc m.loc.label hF).1] at h1
        cases h1
      · rw [hT] at hsto'
        cases hsto'
        exact hN.2 t m hge hmt rfl
    · have hsto' : Eg.sto m.loc.label = some cl := by
        have e := post_sto_old (Eg := Eg) (E' := E') hF
        rw [← e]; exact hsto
      obtain ⟨S0, hRE0, -, hm0, -⟩ := X.inv.thr i th X.hth
      obtain ⟨ρ2, η2, cx2, Rf2, Rs2, hce2, hEO2, hTy2, hTv2, hF2, hRt2, -⟩ := hRE0
      have Y2 : EnvAt p Eg i th (Tot i) S0 ρ2 η2 cx2 Rf2 Rs2 :=
        ⟨hce2, congrArg TEnv.tid hce2, hEO2, hTy2, hTv2, hF2, hRt2⟩
      have hm2 : MemInv (gOf p k arch c i) (CE η2) (stOf c.mem c.pairs th) := by rw [hce2]; exact hm0
      have hs : StepScope cx2 th.term := by
        rcases hsc X Y2 with hs | hR
        · exact hs
        · have hk : r.1 = c.mem := (frame_keep hR hTy2.1 hTy2.2 hF2 hEO2 hTv2 hm2 r X.hr).1
          rw [hk, Array.getElem?_eq_none hge] at hmt; cases hmt
      have hFi : FInv ρ2 η2 th.σs (Resume p th.stack) cx2 th.env :=
        FInvR_FInv (hTv2.2.2.2.2.2.2.2)
          (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs2 E rd ws R h) hF2
      rcases tstep_newPos hEO2 hTy2.1 hTv2 hFi hm2 hs X.hr t m hge hmt with hF1 | hN0
      · exact absurd hF1 hF
      · have hN : NewPos (Cut Eg (gOf p k arch c i).i S0) m.loc := by rw [← hce2]; exact hN0
        obtain ⟨cl1, o, U, us, j, hs2, hat, hus, hrole, hoff⟩ := hN
        have hs3 : Eg.sto m.loc.label = some cl1 := cutSto_sub (i := i) hs2
        rw [hs3] at hsto'
        cases hsto'
        rw [hoff]
        exact role_inWords hat hus (role_lt hrole)

/-- **The promised address lies within its cell's words**: the promise is fulfilled along the
certificate by a single-word write (`certified_promTypedX`, `SWOne_holds`), a `.one` unit of a
component of the cell (as `TermPlantF.promNoTwoP_of`). -/
theorem promWords_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (cl : Cell)
    (hcl : Eg.sto a.label = some cl) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : InWords cl.ty a.offset := by
  obtain ⟨S, hSS⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hSS
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
  have hsc := fun c1 h1 h2 => (hrun X S hSS c1 h1 h2).1
  have hwin := fun c1 h1 h2 => (hrun X S hSS c1 h1 h2).2
  obtain ⟨c1, c2, th1, th2, ρ, η, cx, E2, -, -, -, -, -, -, hx1, hE, hT, htv, hi, hmi, hscope, hpa, -, -, -, -, -,
    -, -, hsw, -⟩ := certified_promTypedX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hX (TermMain.tidAt_cutP X.inv j S) X.cert ht hmt
  obtain ⟨cl1, o1, U, us, j1, hcl1, h1o, hus, hj, ho⟩ :=
    SWOne_holds p _ _ _ _ ρ η cx _ _ hE hT htv hi hmi (TermTyped.scopeD_SW hscope hsw) hpa hsw
  have e : (Cut Eg j S).sto a.label = some cl := hcut
  rw [hx1.2.2.2.2.1 _ _ e] at hcl1
  cases hcl1
  have hoff : a.offset = o1 + j1 := ho
  rw [hoff]
  exact role_inWords h1o hus (TermFul.OneAt_lt hj)

/-- **`MsgWordsG` after a promise step**: old messages unchanged (the plant keeps `sto`), the new
one by `promWords_of`. -/
theorem msgWords_prom (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (h : MsgWordsG Eg c)
    (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) (n : Nat) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    MsgWordsG (EgP Eg P N j n) (promise c j a v w) := by
  intro t m cl hm hsto
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hmem : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by rw [hpi.1]
  have hsto' : Eg.sto m.loc.label = some cl := hsto
  rw [hmem] at hm
  by_cases hlt : t < c.mem.size
  · rw [push_lt hlt] at hm
    exact h t m cl hm hsto'
  · have h1 : t < (c.mem.push ⟨a, v, w⟩).size := (Array.getElem?_eq_some_iff.1 hm).1
    rw [Array.size_push] at h1
    have e : t = c.mem.size := by omega
    subst e
    rw [Array.getElem?_push_size] at hm
    cases hm
    exact promWords_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X cl hsto'

end

/-- (msgWords) A non-promise message at an own cell without a frontier of the thread lies in
the cell (`InCell`). -/
def MsgInCell (E : TEnv) (s : St) : Prop :=
  ∀ (t : Ts) (m : Msg) (cl : Cell), t ∉ s.promises → s.mem[t]? = some m → E.sto m.loc.label = some cl →
    cl.owner = some E.tid → E.pfr m.loc.label = none → TermCohLe.InCell cl.ty m.loc.offset

/-- **`MsgInCell` at every thread**: the owner's `CellOK` words (`OwnOKSF`, at any cut: the cut's
cells do not depend on `seen`) cover the cell's words, and the message lies within them
(`msgWords`). -/
theorem msgInCell_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) {j : Nat} {th : TTh} (hth : c.ths[j]? = some th)
    (S : AllocLabel → Prop) : MsgInCell (Cut Eg j S) (stOf c.mem c.pairs th) := by
  intro t m cl _ hm hsto hown _
  obtain ⟨S0, -, -, hm0, -⟩ := h.thr j th hth
  have hsto0 : (Cut Eg j S0).sto m.loc.label = some cl := hsto
  obtain ⟨vals, hcok, -⟩ := hm0.2.1 m.loc.label cl hsto0 hown
  have hw := h.msgWords t m cl hm (cutSto_sub (i := j) hsto)
  refine ⟨_, _, vals, hcok, ?_⟩
  rcases hcok with ⟨hwc, -⟩ | ⟨N, e, us, hT, hus, -, hl, -⟩
  · obtain ⟨L, hL, hn⟩ := wc_some hwc
    have := hw.1 L hL
    omega
  · have := hw.2 N e us hT hus
    omega

#print axioms wordOK_inWords
#print axioms role_inWords
#print axioms msgWords_thread
#print axioms promWords_of
#print axioms msgWords_prom
#print axioms msgInCell_of

end TermMsgWords
