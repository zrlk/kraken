import WeakCore.TermFulCntR
import WeakCore.TermCntPub
import WeakCore.TermBufPW
import WeakCore.TermAdaptPW

/-! # TermFulCntROf: `FulCntR` holds

The data word `w = ws[j]` a typed thread writes (a one-word unit `j` of the units `us` written at
`b`) lands in a component `U` (at `b`'s offset) of its cell's type, with `accs U = us` and the
operand's runtime type `rt` counting as `U` (`PWAt`).  A counted slot (`CntOK`) of the cell at
`b + j` holding `w`'s value is then counted in the operand (`cnt_core`: segment uniqueness,
`cnt_atOff`, unit-locality `cnt_window` at the `.one` unit), so `cnt_pubWords` gives a counted word
of the operand naming the label with `w`'s `rts`.  Word stores and word `cas`es: the operand is
an integer (`sNo`), all its words count.
Helpers from the team: `TermBufPW` (buffer ops), `TermAdaptPW` (region adaptation).
-/

namespace TermFulCntROf
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermPtrRts TermOwnG0Defs TermCntLoc TermCntEmb
open TermClose (cl clM clI Clo tb)
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The write's target and the operand's counting: a component `U` of `b`'s cell at `b`'s offset,
of units `us`, counting as the operand's runtime type `rt` (same words), `rt` of `U`'s width. -/
def PWAt (η : TEnv) (b : Address) (us : List Acc) (rt : Ty) (ws : List Word) : Prop :=
  ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ accs U = some us ∧
    (∀ L, pubWords U L = pubWords rt L) ∧ wc rt = wc U ∧ ShapeC rt ws

theorem oneAt_unitAt {us : List Acc} {j : Nat} (h : TermFul.OneAt us j) : UnitAt us j = some (.one, 0) := by
  induction h with
  | here _ => simp [UnitAt, Acc.size]
  | cons u _ ih =>
    simp only [UnitAt, Nat.not_lt.2 (Nat.le_add_left u.size _), ite_false, Nat.add_sub_cancel]
    exact ih

theorem pubWords_Fd {T U : Ty} (h : Fd T U) : ∀ L, pubWords T L = pubWords U L := by
  induction h with
  | refl => intro L; rfl
  | fold hW hg _ _ ih => intro L; rw [ih L]; exact TermCntEmb.pubWords_cl_unfold hW hg L

theorem guardT_adapt : ∀ (u : Ty) (r : Idx) (k : Nat), (adapt r u).guardT k = u.guardT k := by
  intro u
  induction u with
  | ptr μ t _ => intro r k; cases μ <;> rfl
  | ptrOpt μ t _ => intro r k; cases μ <;> rfl
  | loc μ t _ => intro r k; cases μ <;> rfl
  | prod a b iha ihb => intro r k; simp only [adapt, Ty.guardT, iha, ihb]
  | sum a b iha ihb => intro r k; simp only [adapt, Ty.guardT, iha, ihb]
  | array i t ih => intro r k; simp only [adapt, Ty.guardT, ih]
  | iex t ih => intro r k; simp only [adapt, Ty.guardT, ih]
  | iall t ih => intro r k; simp only [adapt, Ty.guardT, ih]
  | tex κ t ih => intro r k; simp only [adapt, Ty.guardT, ih]
  | refine t ψ ih => intro r k; simp only [adapt, Ty.guardT, ih]
  | mu t ih => intro r k; simp only [adapt, Ty.guardT, ih]
  | _ => intro r k; rfl

/-- **The counting transfer**: a counted slot at offset `o + j` of a cell of type `T`, holding
`w`'s value, where `U` is the component at `o` (units `us`, `j` a one-word unit), is counted at
`j` in any value `ws ∋ w` of a type `rt` counting as `U`. -/
theorem cnt_core {T U rt : Ty} {o j off : Nat} {us : List Acc} {ws : List Word} {w w0 : Word}
    (hat : AtOff T o U) (hus : accs U = some us) (hpw : ∀ L, pubWords U L = pubWords rt L)
    (hwc : wc rt = wc U) (hsh : ShapeC rt ws) (hone : TermFul.OneAt us j) (hwj : ws[j]? = some w)
    (hoff : off = o + j) (hC : CntOK T off w0) (hv : w0.val = w.val) : j ∈ cntIdx rt ws := by
  obtain ⟨b0, S, ws0, o', hseg, hsh0, hw0, ho, hc⟩ := hC
  have hj : j < nWords us := TermFul.OneAt_lt hone
  obtain ⟨L, hL⟩ := segOf_accs hseg
  obtain ⟨b1, S1, o1, L1, hseg1, hL1, hat1, hb1⟩ :
      ∃ b1 S1 o1 L1, SegOf T b1 S1 ∧ accs S1 = some L1 ∧ AtOff S1 o1 U ∧ b1 + o1 = o := by
    have hseg' := hseg
    rcases hseg with ⟨rfl, rfl, -⟩ | ⟨N, usS, jj, hT, -, -, -⟩
    · exact ⟨0, _, o, L, hseg', hL, hat, by omega⟩
    · rcases AtOff_arr_elem hat hT with hUT | ⟨us', j', o'', hacc', hj', hoe, hat'⟩
      · rw [hUT, hT] at hus; simp [accs] at hus
      · exact ⟨j' * nWords us', _, o'', us', Or.inr ⟨N, us', j', hT, hacc', hj', rfl⟩, hacc', hat', hoe.symm⟩
  have hlen0 : ws0.length = nWords L := hsh0 L hL
  have hlt0 : o' < nWords L := by have := (List.getElem?_eq_some_iff.1 hw0).1; omega
  obtain ⟨pre, post, eL, hpre⟩ := AtOff_embed hat1 hL1 hus
  have hn1 : nWords L1 = nWords pre + nWords us + nWords post := by
    rw [eL]; simp only [nWords, List.map_append, List.sum_append]
  have hlt1 : o1 + j < nWords L1 := by omega
  obtain ⟨rfl, rfl⟩ := SegOf_unique2 hseg hL hlt0 hseg1 hL1 hlt1 (by omega)
  have hLL : L = L1 := by rw [hL] at hL1; exact Option.some.inj hL1
  subst hLL
  have ho' : o' = o1 + j := by omega
  subst ho'
  rw [cntIdx_eq] at hc ⊢
  have h1 := cnt_atOff hat1 hL hus 0 ws0 hlen0 j hj
  simp only [Nat.add_zero] at h1
  have h2 := h1.1 hc
  rw [show o1 + j = j + o1 by omega, mem_cntK_shift] at h2
  have hwl : ((ws0.drop o1).take (nWords us)).length = nWords us := by
    simp only [List.length_take, List.length_drop]; omega
  have hwsl : ws.length = nWords us := ShapeC_len hsh (by rw [hwc]; simp [wc, hus])
  have hwj0 : ((ws0.drop o1).take (nWords us))[j]? = some w0 := by
    rw [List.getElem?_take_of_lt hj, List.getElem?_drop]; exact hw0
  have hveq : VEq ((((ws0.drop o1).take (nWords us)).drop (j - 0)).take (0 + 1)) ((ws.drop (j - 0)).take (0 + 1)) := by
    simp only [Nat.sub_zero, Nat.zero_add]
    rw [take_drop_one hwj0, take_drop_one hwj]
    simp [VEq, hv]
  have h3 := cnt_window U us hus 0 _ ws j 0 .one hwl (by omega) (oneAt_unitAt hone) hveq
  simp only [Nat.add_zero] at h3
  have h4 := h3.1 h2
  rwa [cntK_congr hpw] at h4

/-- From `PWAt` and a counted slot at the written word: a counted word of the operand. -/
theorem fin {η : TEnv} {sto : Sto} {b : Address} {us : List Acc} {rt : Ty} {ws : List Word} {j : Nat}
    {w : Word} {m : Msg} {cl : Cell} {a : AllocLabel}
    (hsto : ∀ l c, η.sto l = some c → sto l = some c) (hP : PWAt η b us rt ws)
    (hone : TermFul.OneAt us j) (hwj : ws[j]? = some w) (hl : m.loc = offs b j) (hv : m.val = w.val)
    (hn : Names a w) (hcl : sto m.loc.label = some cl) (hc : CntOK cl.ty m.loc.offset (mw m)) :
    ∃ w' ∈ pubWords rt ws, Names a w' ∧ w'.rts = w.rts := by
  obtain ⟨c, U, hs, hat, hus, hpw, hwc, hsh⟩ := hP
  rw [hl] at hcl hc
  have hcl' : sto b.label = some cl := hcl
  have e : cl = c := by
    have := hsto _ _ hs
    rw [hcl'] at this; exact Option.some.inj this
  subst e
  exact TermCntPub.cnt_pubWords (cnt_core hat hus hpw hwc hsh hone hwj rfl hc hv) hwj hn

/-- A cell operation through a pointer/locative at `t` (pointee `u`), of a variable at a subtype of
`u` or of its region adaptation. -/
theorem cell_pw {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx c₁ : Cx}
    {env : Env} {a : At} {x : String} {t u t0 tv rt : Ty} {μ : Mode} {ws : List Word} {pw : Word}
    {b : Address} {us : List Acc}
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx) (hp : cx.peek a = .ok t) (hc : cellOf t = some (μ, u))
    (hu : cx.use (.var x) = .ok (tv, c₁)) (hsub : SubS c₁ tv u ∨ ∃ r, SubS c₁ tv (adapt r u))
    (hlk : lookupE env x = some (rt, ws)) (hea : evalAt env a = some (t0, [pw])) (hb : addrOf pw = some b)
    (hacc : cx.opaqueOK u = true → accs (cl ρ η.wit 0 0 u) = some us) :
    PWAt η b us rt ws := by
  obtain ⟨c, U, hsto, hat, hFd⟩ := ptr_target hi.2.1 hp (cell_cases hc) hea hb
  obtain ⟨-, rt', ws', hev, -, hl⟩ := use_FInv hu hi
  simp only [evalAt, hlk, Option.some.injEq, Prod.mk.injEq] at hev
  obtain ⟨rfl, rfl⟩ := hev
  have htb := tb_cellOf (peek_tb htv hp) hc
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu).1
  have key : cx.opaqueOK u = true ∧ (∀ L, pubWords (cl ρ η.wit 0 0 u) L = pubWords rt L) ∧
      wc rt = wc (cl ρ η.wit 0 0 u) := by
    rcases hsub with hsub | ⟨r, hsub⟩
    · have ho := sub_opaqueOK hsub hotv
      exact ⟨ho, TermBufPW.pw_chain hi hl hsub ho htb⟩
    · have ho' := sub_opaqueOK hsub hotv
      have ho : cx.opaqueOK u = true := by
        unfold Cx.opaqueOK at ho' ⊢; simpa only [guardT_adapt] using ho'
      have h2 := TermBufPW.pw_chain hi hl hsub ho' (by rw [tb_adapt]; exact htb)
      have h3 := TermAdaptPW.pubWords_cl_adapt0 u r ρ η.wit
      exact ⟨ho, fun L => (h3.1 L).symm.trans (h2.1 L), h2.2.trans h3.2⟩
  obtain ⟨ho, hpw, hwc⟩ := key
  refine ⟨c, U, hsto, hat, by rw [Fd_accs hFd]; exact hacc ho, fun L => (pubWords_Fd hFd L).trans (hpw L),
    hwc.trans (by unfold wc; rw [Fd_accs hFd]), hl.1⟩

/-- **`FulCntR` holds.** -/
theorem fulCntR_of (p : Prog) : TermK2a.FulCntR p := by
  intro E sto g mem pairs th x rt ws w m cl a h1 hT _ hW hv hn hcl _ hcnt
  obtain ⟨ρ, η, cx, hE, hEo, hTy, htv, hi, -⟩ := hT
  subst hE
  have hsto' : ∀ l c, η.sto l = some c → sto l = some c := h1
  have hfast : sNo rt = true → ∃ w' ∈ pubWords rt ws, Names a w' ∧ w'.rts = w.rts := fun hs =>
    ⟨w, by rw [pubWords_of_sNo hs]; exact hW.2.1, hn, rfl⟩
  obtain ⟨hlk, -, ⟨y, op, e, pw, b, rel, us, j, hterm, hdv, hU, hOne, hwj, hl⟩ |
    ⟨acq, rel, wa, e, tn, ok, fail, t1, t2, pw, ew, hterm, hws, hwa, -, hpw⟩⟩ := hW
  · have hfin : PWAt η b us rt ws → ∃ w' ∈ pubWords rt ws, Names a w' ∧ w'.rts = w.rts :=
      fun hP => fin hsto' hP hOne hwj hl hv hn hcl hcnt
    rw [hterm] at hTy
    cases hTy with
    | let_ hop _ =>
    have hop' := hop
    cases hop with
    | storeOwn hpk _ hc0 _ hu hsub _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, hea, -, hcr, hb, hus⟩ := hU
      exact hfin (cell_pw hi htv hpk hc0 hu (Or.inl hsub) hlk hea hb fun ho =>
        (pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hEo.2.1 k).1) hi.2.1 htv hpk hc0 ho hea hcr).symm.trans hus)
    | storePub hpk _ hc0 _ hu hsub _ _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, hea, -, hcr, hb, hus⟩ := hU
      exact hfin (cell_pw hi htv hpk hc0 hu (Or.inl hsub) hlk hea hb fun ho =>
        (pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hEo.2.1 k).1) hi.2.1 htv hpk hc0 ho hea hcr).symm.trans hus)
    | storeRgn hpk _ hc0 _ hu _ hsub _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, hea, -, hcr, hb, hus⟩ := hU
      exact hfin (cell_pw hi htv hpk hc0 hu (hsub.imp id fun h => ⟨_, h⟩) hlk hea hb fun ho =>
        (pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hEo.2.1 k).1) hi.2.1 htv hpk hc0 ho hea hcr).symm.trans hus)
    | storeCap hpk _ hc0 _ hu _ _ hsub _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, hea, -, hcr, hb, hus⟩ := hU
      exact hfin (cell_pw hi htv hpk hc0 hu (hsub.imp id fun h => ⟨_, h⟩) hlk hea hb fun ho =>
        (pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hEo.2.1 k).1) hi.2.1 htv hpk hc0 ho hea hcr).symm.trans hus)
    | storeWordGive _ _ hu _ hii _ _ _ _ _ _ _ _ _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      exact hfast (TermPubOnly.sNo_word hi hu hii hlk)
    | storeWordKeep _ _ hu _ hii _ _ _ _ _ _ _ _ _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      exact hfast (TermPubOnly.sNo_word hi hu hii hlk)
    | storeWordHand _ _ hu _ hii _ _ _ _ _ _ _ _ _ _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      exact hfast (TermPubOnly.sNo_word hi hu hii hlk)
    | xchg hpk hxc hu hsub _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, hea, -, hcr, hb, hus⟩ := hU
      cases hxc with
      | own _ hc0 _ =>
        exact hfin (cell_pw hi htv hpk hc0 hu (Or.inl (hsub.elim id id)) hlk hea hb fun ho =>
          (pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hEo.2.1 k).1) hi.2.1 htv hpk hc0 ho hea hcr).symm.trans hus)
      | rgn _ hc0 _ _ _ =>
        exact hfin (cell_pw hi htv hpk hc0 hu (hsub.imp id fun h => ⟨_, h⟩) hlk hea hb fun ho =>
          (pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hEo.2.1 k).1) hi.2.1 htv hpk hc0 ho hea hcr).symm.trans hus)
    | xchgAt =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      exact hfin (TermBufPW.xchgAt_pw hop' hi hEo htv hU hlk)
    | xchgAtF =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      exact hfin (TermBufPW.xchgAtF_pw hop' hi hEo htv hU hlk)
    | bufInit =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      exact hfin (TermBufPW.bufInit_pw hop' hi hEo htv hU hlk)
    | _ => simp [TermNoFul.DataVar] at hdv
  · rw [hterm] at hTy
    subst hws
    cases hTy with
    | casCell hpk _ hc0 hraw _ _ hu _ hsub _ _ _ _ =>
      have hP : PWAt η m.loc [.one] rt [w] := by
        rcases hc0 with hc0 | ⟨_, hc0, _⟩
        · exact cell_pw hi htv hpk hc0 hu (Or.inl hsub) hlk hwa hpw fun _ => accs_cl_one hraw
        · exact cell_pw hi htv hpk hc0 hu (Or.inl hsub) hlk hwa hpw fun _ => accs_cl_one hraw
      exact fin hsto' hP (.here _) rfl (by simp [offs]) hv hn hcl hcnt
    | casShare _ _ _ _ hii _ _ _ _ _ _ _ _ _ _ => exact hfast (TermPubOnly.sNo_wordP hi hii hlk)
    | casTake _ _ _ _ hii _ _ _ _ _ _ _ _ _ _ _ _ _ => exact hfast (TermPubOnly.sNo_wordP hi hii hlk)
    | casEpoch _ _ _ _ _ hii _ _ _ _ _ _ => exact hfast (TermPubOnly.sNo_wordP hi hii hlk)

end TermFulCntROf

#print axioms TermFulCntROf.cnt_core
#print axioms TermFulCntROf.cell_pw
#print axioms TermFulCntROf.fulCntR_of
