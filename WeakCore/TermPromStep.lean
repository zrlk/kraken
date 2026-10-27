import WeakCore.TermNoHold
import WeakCore.TermPlantF
import WeakCore.TermBal

/-!
# TermPromStep: the promise step's side conditions `hwu`, `hfw`

The side conditions `hwu`/`hfw` of the promise step (`HWU`/`HFW`, at the
promiser's cut `Cut Eg j S`, `tstepMC_promEc`), formerly `ObligationsF` fields.

* `firstW_core`: at a predicted unit of a `.one` unit of a buffer, some message
  is not `undef`, hence (`firstW_of_exists`) there is a first write.  The latest
  message there is not an own promise (`PromNotUndef`), nor a placeholder (`HiddenP`,
  `PubDefP`/`OwnHidP`, would give a later message).
* `hfw_of`: the `.one` unit from the certificate (`SWOne_holds`).
* `hwu_of`: `PromNewOK` (initialised, a typed word of the planted public
  environment; no plant at a shared label, `PlantSpec`), `word2` units excluded
  by the `.one` unit.
-/

namespace TermPromStep
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## 1. Memory: first and last messages at an address -/

/-- A message at `a` that is not `undef` gives a first write at `a`. -/
theorem firstW_of_exists {mem : Memory} {a : Address} :
    ∀ (t : Nat) (m : Msg), mem[t]? = some m → m.loc = a → m.val ≠ .undef → ∃ h, FirstW mem a h := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro m hm hl hv
    by_cases hb : ∃ (t' : Nat) (m' : Msg), t' < t ∧ mem[t']? = some m' ∧ m'.loc = a ∧ m'.val ≠ .undef
    · obtain ⟨t', m', hlt, h1, h2, h3⟩ := hb
      exact ih t' hlt m' h1 h2 h3
    · refine ⟨t, ⟨m, hm, hl, hv⟩, fun t' m' hlt h1 h2 => ?_⟩
      exact Classical.byContradiction fun h3 => hb ⟨t', m', hlt, h1, h2, h3⟩

/-- A message at `a` gives a last message at `a`. -/
theorem lastMsg {mem : Memory} {a : Address} :
    ∀ (d t : Nat) (m : Msg), mem.size ≤ t + d → mem[t]? = some m → m.loc = a →
      ∃ (t1 : Nat) (m1 : Msg), mem[t1]? = some m1 ∧ m1.loc = a ∧
        ∀ (t2 : Nat) (m2 : Msg), t1 < t2 → mem[t2]? = some m2 → m2.loc ≠ a := by
  intro d
  induction d with
  | zero =>
    intro t m hs hm _
    have := (Array.getElem?_eq_some_iff.1 hm).1
    omega
  | succ d ih =>
    intro t m hs hm hl
    by_cases hb : ∃ (t2 : Nat) (m2 : Msg), t < t2 ∧ mem[t2]? = some m2 ∧ m2.loc = a
    · obtain ⟨t2, m2, hlt, h1, h2⟩ := hb
      exact ih t2 m2 (by omega) h1 h2
    · exact ⟨t, m, hm, hl, fun t2 m2 hlt h1 h2 => hb ⟨t2, m2, hlt, h1, h2⟩⟩

/-! ## 2. Layout: `undef` is no word at a `.one` unit -/

/-- `undef` is no `WordOK` word at a `.one` unit of a component of the cell type. -/
theorem undef_nwordOK_one {E : TEnv} {T U : Ty} {o j : Nat} {us : List Acc} {w : Word}
    (h1 : AtOff T o U) (hus : accs U = some us) (hj : TermFul.OneAt us j) (hw : w.val = .undef) :
    ¬ WordOK E T (o + j) w := by
  intro h
  obtain ⟨b, S, ws, o', w0, hseg, ⟨⟨hvr, -⟩, hsh⟩, hw0, hle, hbo⟩ := h
  have hlt0 : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
  obtain ⟨L, hL, hone⟩ : ∃ L, accs S = some L ∧ TermFul.OneAt L o' := by
    rcases hseg with ⟨rfl, rfl, hT⟩ | ⟨N, uS, jj, rfl, huS, hjj, rfl⟩
    · obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.1 hT
      obtain ⟨pre, post, e, hn⟩ := AtOff_embed h1 hL hus
      refine ⟨L, hL, ?_⟩
      have e2 : o' = nWords pre + j := by omega
      rw [e, e2]
      exact TermPlantF.oneAtF_append post (TermPlantF.oneAtF_prepend pre hj)
    · rcases AtOff_arr_elem h1 rfl with hU | ⟨us', j2, o'', hus', hj2, ho, hat⟩
      · subst hU; simp [accs] at hus
      · rw [huS] at hus'
        cases hus'
        obtain ⟨pre, post, e, hn⟩ := AtOff_embed hat huS hus
        have hb1 : o'' + nWords us ≤ nWords uS := AtOff_bound hat huS hus
        have hb2 : j < nWords us := TermFul.OneAt_lt hj
        have hb3 : o' < nWords uS := hsh uS huS ▸ hlt0
        have e2 : o' = o'' + j := by
          rcases Nat.lt_trichotomy j2 jj with hlt | rfl | hgt
          · have hm : (j2 + 1) * nWords uS ≤ jj * nWords uS := Nat.mul_le_mul_right _ hlt
            rw [Nat.succ_mul] at hm
            omega
          · omega
          · have hm : (jj + 1) * nWords uS ≤ j2 * nWords uS := Nat.mul_le_mul_right _ hgt
            rw [Nat.succ_mul] at hm
            omega
        refine ⟨uS, huS, ?_⟩
        rw [e, e2, ← hn]
        exact TermPlantF.oneAtF_append post (TermPlantF.oneAtF_prepend pre hj)
  have hnu := VR_one_nundef S hvr hL
  exact hnu o' w0 hone hw0 (hle.1.trans hw)

/-! ## 3. The first write at a predicted `.one` unit -/

/-- **(hfw core)** At a predicted unit `a` lying in a `.one` unit of its
buffer's slot type, with no own promise `undef`, there is a first write. -/
theorem firstW_core {g : G} {E : TEnv} {s : St} {a : Address} {c : Cell} {N : Nat} {e : Ty} {ue : List Acc}
    {U : Ty} {us : List Acc} {o j : Nat}
    (hm : MemInv g E s) (hq : PredU E a) (hc : E.sto a.label = some c) (hT : c.ty = .array (.lit N) e)
    (hue : accs e = some ue) (h1o : AtOff c.ty o U) (hus : accs U = some us) (hj : TermFul.OneAt us j)
    (ho : a.offset = o + j)
    (hnu : ∀ (t : Nat) (m : Msg), t ∈ s.promises → s.mem[t]? = some m → m.val ≠ .undef) :
    ∃ h, FirstW s.mem a h := by
  obtain ⟨ofs, hofs⟩ : ∃ x : Nat, a.offset = x := ⟨_, rfl⟩
  rcases AtOff_arr_elem h1o hT with hU | ⟨ue', j2, o'', hue', hj2, hoe, hat⟩
  · rw [hU, hT] at hus; simp [accs] at hus
  rw [hue] at hue'
  cases hue'
  have hb1 : o'' + nWords us ≤ nWords ue := AtOff_bound hat hue hus
  have hb2 : j < nWords us := TermFul.OneAt_lt hj
  have hIni : ofs < E.ini a.label * nWords ue := hofs ▸ hq.2.1 c N e ue hc hT hue
  have hrc : E.rc a.label < E.ini a.label := by
    refine Nat.lt_of_not_le fun hle => hq.2.2 fun c' N' e' us' hc' hT' hus' => ?_
    rw [hc] at hc'
    cases hc'
    rw [hT] at hT'
    cases hT'
    rw [hue] at hus'
    cases hus'
    rw [hofs]
    exact Nat.lt_of_lt_of_le hIni (Nat.mul_le_mul_right _ hle)
  have hInit : InitR E c a.label a.offset := fun N' e' us' hT' hus' => hq.2.1 c N' e' us' hc hT' hus'
  have hoj : ofs = o + j := by rw [← hofs]; exact ho
  have hofs2 : ofs = j2 * nWords ue + (o'' + j) := by omega
  have hN : ofs < N * nWords ue := by
    have hm : (j2 + 1) * nWords ue ≤ N * nWords ue := Nat.mul_le_mul_right _ hj2
    rw [Nat.succ_mul] at hm
    omega
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hq.1
  -- a placeholder below `f` is overwritten, and some message lies at `a`
  obtain ⟨f', hH, t0, m0, hm0, hl0⟩ : ∃ f', HiddenP E c.ty s.mem s.promises a.label a.offset f' ∧
      ∃ (t : Nat) (m : Msg), s.mem[t]? = some m ∧ m.loc = a := by
    by_cases hown : c.owner = some E.tid
    · obtain ⟨f1, -, -, hh⟩ := hm.2.2.2.2.2.1.2 a.label c hc hown hrc
      refine ⟨f1, hh a.offset hInit, ?_⟩
      obtain ⟨vals, hcell, hlat, -⟩ := hm.2.1 a.label c hc hown
      rcases hcell with ⟨hw, -⟩ | ⟨N', e', us', hT', hus', -, hlen, -⟩
      · rw [hT] at hw; simp [wc, accs] at hw
      · rw [hT] at hT'
        cases hT'
        rw [hue] at hus'
        cases hus'
        have hlt : ofs < vals.length := by rw [hlen]; exact hN
        have hv : vals[a.offset]? = some vals[ofs] := by rw [hofs]; exact List.getElem?_eq_getElem hlt
        obtain ⟨⟨m, hm1, hl1, -⟩, -⟩ := hlat a.offset _ hv
        exact ⟨_, m, hm1, hl1⟩
    · refine ⟨f, hm.2.2.2.2.2.2.1 a.label c f hc hown hf a.offset hInit, ?_⟩
      have hseg : SegOf c.ty (j2 * nWords ue) e := Or.inr ⟨N, ue, j2, hT, hue, hj2, rfl⟩
      obtain ⟨t, m, hm1, hl1⟩ := hm.2.2.2.2.2.2.2.2.1.2.2.2.2 a.label c f (j2 * nWords ue) e ue (o'' + j) hc hown hf
        hseg hue (by omega)
      refine ⟨t, m, hm1, ?_⟩
      rw [hl1, ← hofs2, ← hofs]
  refine Classical.byContradiction fun hno => ?_
  have hall : ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc = a → m.val = .undef := fun t m h1 h2 =>
    Classical.byContradiction fun h3 => hno (firstW_of_exists t m h1 h2 h3)
  obtain ⟨t, m, hm1, hl, hmax⟩ := lastMsg s.mem.size t0 m0 (Nat.le_add_left _ _) hm0 hl0
  have hund : m.val = .undef := hall t m hm1 hl
  by_cases htp : t ∈ s.promises
  · exact hnu t m htp hm1 hund
  · have hnw : ¬ WordOK E c.ty a.offset (mw m) := by
      rw [ho]; exact undef_nwordOK_one h1o hus hj hund
    obtain ⟨t', m', hlt, -, hm', hl'⟩ := hH t m htp hm1 hl hnw
    exact hmax t' m' hlt hm' hl'

/-! ## 4. The side conditions at the promiser's cut -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (B5) The certificate at the promiser's own environment `CE η`: the promised
address lies in a `.one` unit of its cell there (`SWOne_holds`). -/
theorem prom_oneAt (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {η : TEnv} {S : AllocLabel → Prop} (hCE : CE η = Cut Eg j S) {cl : Cell} (hcl : (CE η).sto a.label = some cl) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ o U us j1, AtOff cl.ty o U ∧ accs U = some us ∧ TermFul.OneAt us j1 ∧ a.offset = o + j1 := by
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  obtain ⟨S0, hS0⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTEs, hmS, -⟩ := id hS0
  have hSCs : StoClo (Cut Eg j S0) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  obtain ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, -, -, -, hIH0⟩ := TermNoHold.InvAtXF_of (p := p) (k := k)
    (arch := arch) hpi.2.1 hTEs (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hmS) hSCs
    (by rw [gOf_promise]; exact X.inv.bf)
    (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh _ _ _ X.hth))
    (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
      (Nat.sub_le_sub_right (by rw [hpi.1]; show c.mem.size ≤ (c.mem.push _).size; rw [Array.size_push]; exact Nat.le_succ _) 1))
  have hcl0 : (Cut Eg j S0).sto a.label = some cl := by rw [hCE] at hcl; exact hcl
  have hX : InvAtX p k arch j (Cut Eg j S0) _ _ (promise c j a v w) :=
    ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, fun _ _ _ h => h.elim, hIH0⟩
  have hsc := fun c1 h1 h2 => (hrun X S0 hS0 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => (hrun X S0 hS0 c1 h1 h2).2
  have ht : c.mem.size ∈ TermFul.promsOf (promise c j a v w) j := by
    rw [TermFul.promsOf_some hpi.2.1]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hmt : (promise c j a v w).mem[c.mem.size]? = some ⟨a, v, w⟩ := by
    rw [hpi.1]; exact Array.getElem?_push_size
  obtain ⟨c1, c2, th1, th2, ρ1, η1, cx1, E2, -, -, -, -, -, -, hx1, hE, hT, htv, hi, hmi, hscope, hpa, -, -, -, -, -,
    -, -, hsw, -⟩ := certified_promTypedX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hX (TermMain.tidAt_cutP X.inv j S0) X.cert ht hmt
  obtain ⟨cl1, o1, U, us, j1, hcl1, h1o, hus, hj, ho⟩ :=
    SWOne_holds p _ _ _ _ ρ1 η1 cx1 _ _ hE hT htv hi hmi (TermTyped.scopeD_SW hscope hsw) hpa hsw
  rw [hx1.2.2.2.2.1 _ _ hcl0] at hcl1
  cases hcl1
  exact ⟨o1, U, us, j1, h1o, hus, hj, ho⟩

/-- **`hfw`** at the promiser's cut. -/
theorem hfw_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (S : AllocLabel → Prop) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S) := by
  intro η hCE hRE hm hq
  have hSC : StoClo (CE η) := by rw [hCE]; exact fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  obtain ⟨cl, N, e, ue, hc, hT, hue⟩ : ∃ cl N e ue, (CE η).sto a.label = some cl ∧ cl.ty = .array (.lit N) e ∧
      accs e = some ue :=
    Classical.byContradiction fun hn => hq.2.2 fun c' N' e' us' h1 h2 h3 => absurd ⟨c', N', e', us', h1, h2, h3⟩ hn
  obtain ⟨o, U, us, j1, h1o, hus, hj, ho⟩ := prom_oneAt (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hCE hc
  exact firstW_core hm hq hc hT hue h1o hus hj ho (fun t m ht hmt => X.inv.promNU j th t m X.hth ht hmt)


/-- **`hwu`** at the promiser's cut: the new promise's `PromNewOK` (initialised, a
typed word in the planted public environment, no plant at a visible label),
the `.one` unit from the certificate excluding `word2` units. -/
theorem hwu_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
    {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
    (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf)
    (hnew : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 plantOf plantN)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (S : AllocLabel → Prop) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S) := by
  intro η hCE hRE hm hvis
  have hSC : StoClo (CE η) := by rw [hCE]; exact fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  obtain ⟨⟨cl, hcl, hwu⟩, hvisl⟩ := hvis
  have hcl' : cutSto Eg j a.label = some cl := by rw [hCE] at hcl; exact hcl
  have hclg : Eg.sto a.label = some cl := cutSto_sub hcl'
  have hsh : Eg.Shared a.label := by
    by_cases hpf : Eg.pfr a.label = none
    · rcases (cutSto_some.1 hcl').2 with hown | hs
      · exfalso
        refine hvisl ⟨⟨cl, hcl, ?_⟩, ?_⟩
        · rw [hCE]; exact hown
        · rw [hCE]; exact hpf
      · exact hs
    · exact Option.ne_none_iff_exists'.1 hpf
  have hP0 : plantOf c Eg j a v w a.label = none := by
    cases e : plantOf c Eg j a v w a.label with
    | none => rfl
    | some f =>
      exfalso
      obtain ⟨hpf, -⟩ := hspec X a.label f e
      obtain ⟨f', hf'⟩ := hsh
      rw [hpf] at hf'
      cases hf'
  have hshP : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared a.label := by
    obtain ⟨f, hf⟩ := hsh
    exact ⟨f, by simp [EgP, plantG, TermCut.GEnv.withFp, hP0, hf]⟩
  have hini : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).ini a.label = Eg.ini a.label := by
    simp [EgP, plantG, TermCut.GEnv.withFp, hP0]
  obtain ⟨hinit, hwok⟩ := hnew X cl hclg hshP
  obtain ⟨o, U, us, j1, h1o, hus, hj, ho⟩ := prom_oneAt (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hCE hcl
  have hiw : IniW (CE η) a := by
    intro c' N e us' hc' hT hus'
    rw [hcl] at hc'
    cases hc'
    have h1 := hinit N e us' hT hus'
    have h2 : (CE η).ini = Eg.ini := by rw [hCE]; rfl
    rw [h2]
    have h3 : (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)).ini a.label =
        Eg.ini a.label := hini
    rw [h3] at h1
    exact h1
  rcases hwu with ⟨r, P, hg, hat⟩ | ⟨r, P, hat⟩ | ⟨r, P, h1, hat⟩
  · obtain ⟨n, rfl⟩ := AtOff_word_lit hat (hSC a.label cl hcl) r P rfl
    obtain ⟨hpwf, kk, hk, hin⟩ := wordOK_word hwok hat hg
    exact ⟨cl, n, P, hcl, hat, hg, IniAt_of_IniW hcl hat hiw, _, VRR_word_of hpwf ⟨kk, hk, hin⟩⟩
  · exfalso
    have h2 := (TermGlob.oneAt_word2 h1o hus hj hat).1
    exact h2 ho.symm
  · exfalso
    have h2 := (TermGlob.oneAt_word2 h1o hus hj hat).2
    obtain ⟨x, hx⟩ : ∃ x : Nat, a.offset = x := ⟨_, rfl⟩
    have ho' : x = o + j1 := by rw [← hx]; exact ho
    have h1' : 1 ≤ x := by rw [← hx]; exact h1
    apply h2
    rw [hx]
    omega

end

/-- **`allocG`** (F2′): an own key minted by a thread step is at one of the stepper's fresh
labels.  The only `MintStep` constructor minting `.own l` is `alloc`, which carries
`FreshIn g th.nalloc r.2.2.nalloc l` for the step's own `g` (the (H) `MintStep g` index). -/
theorem allocG_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} :
    TermBal.AllocGT p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z l hF
  have hMS : MintStep (gOf p k arch c i) η (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) C F :=
    Z.2.2.2.2.2.2.1
  cases hMS with
  | @alloc l' hf _ =>
    have e : l' = l := Classical.byContradiction fun hne => hF (by simp [Res.one_apply, Ne.symm hne])
    subst e
    exact hf
  | fresh => exact absurd (by simp [Res.add_apply, Res.one_apply]) hF
  | _ => exact absurd (by simp [Res.one_apply]) hF

end TermPromStep

#print axioms TermPromStep.firstW_of_exists
#print axioms TermPromStep.lastMsg
#print axioms TermPromStep.undef_nwordOK_one
#print axioms TermPromStep.firstW_core
#print axioms TermPromStep.prom_oneAt
#print axioms TermPromStep.hfw_of
#print axioms TermPromStep.hwu_of
#print axioms TermMain.tstepMC_promEc
#print axioms TermPromStep.allocG_of
