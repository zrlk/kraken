import WeakCore.TermUndefLowF
import WeakCore.TermPromClos

namespace TermUndefLow
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermCert TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §5 A typed thread step's new `undef` messages lie in two-word units -/

/-- **(§5, typed)**: a new `undef` message of a typed, in-scope thread step is at a fresh label of
the step or at a word of a two-word unit of a written component. -/
theorem tstep_newUndef {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} (hP : ProgT p) (hE : EnvOK p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpr : PromAbove (stOf r.1 r.2.1 r.2.2))
    (t : Ts) (m : Msg) (ht : mem.size ≤ t) (hmt : r.1[t]? = some m) (hu : m.val = .undef) :
    FreshIn g th.nalloc r.2.2.nalloc m.loc.label ∨
      ∃ b us jj, TermB5.UnitsAtI η b us ∧ TwoAt us jj ∧ (m.loc = offs b jj ∨ m.loc = offs b (jj + 1)) := by
  rcases tstep_newV (MemInv_promLt hm) hr t m ht hmt with hF | hN
  · exact .inl hF
  right
  rcases hN with ⟨x, op, e, hterm, hN⟩ |
      ⟨acq, rel, w, e, v', tn, ok, fail, tw, pw, te, ew, tv, nw, hterm, hw, he, hv, hb, hval⟩ |
      ⟨acq, rel, w, e0, e1, v0, v1, tn, ok, fail, tw, pw, A, hterm, hea, hb, hl⟩
  · have hT0 := hT
    have hsc0 := hsc
    rw [hterm] at hT0 hsc0
    cases hT0 with
    | let_ hop _ =>
      rcases hN with ⟨pw, b, rel, us, ws, j, hU, hl, hR⟩ |
          ⟨rel, a, v0, v1, tk, t1, pw, b, ws, j, rfl, hea, hb, hl, hR⟩ |
          ⟨o, acq, rel, a, v1, t1, pw, rfl, hea, hb⟩
      · have hua := TermB5.unitsOp_uaI hop hsc0 hi hE htv hU
        rcases hR with ⟨h1, w, hw, hv⟩ | h2 | ⟨jj, rfl, h3⟩
        · exact absurd (hv.symm.trans hu) (TermTyped.unitsOp_nu hop hsc0 hi hE htv hU j w h1 hw)
        · exact ⟨b, us, j, hua, h2, .inl hl⟩
        · exact ⟨b, us, jj, hua, h3, .inr hl⟩
      · have hua := TermB5.stp_uaI hop hsc0 hi hea hb
        rcases hR with ⟨h1, -⟩ | h2 | ⟨jj, rfl, h3⟩
        · exact absurd rfl (TermTyped.oneAt_not_two h1)
        · exact ⟨b, [.two], j, hua, h2, .inl hl⟩
        · exact ⟨b, [.two], jj, hua, h3, .inr hl⟩
      · obtain ⟨n, hn⟩ := fetch_new_num hterm hP hT hi hE htv hm hsc hr hpr t m ht hmt
        rw [hn] at hu
        cases hu
  · rw [hterm] at hT
    exact absurd (hval.symm.trans hu) (TermTyped.cas_nu hT hi hE htv hv)
  · rw [hterm] at hT hsc
    have hua := TermB5.casp_uaI hT hsc hi hea hb
    rcases hl with hl | hl
    · exact ⟨A, [.two], 0, hua, TermB5.twoAt_two0, .inl (hl.trans (TermStepper.offs_zero A).symm)⟩
    · refine ⟨A, [.two], 0, hua, TermB5.twoAt_two0, .inr (hl.trans ?_)⟩
      cases A
      rfl

#print axioms tstep_newUndef

/-! ## §6 At a reachable thread step -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`UndefLowG` across a thread step.**  A new `undef` message at a single-word unit of an old
cell is excluded by typing and layout (`tstep_newUndef`, `two_not_oneU`); at a fresh label, an old
message is a promise of the stepper (`GFreshL`), not `undef` (`promNU`), and not outstanding after
the step (`PromAllocF`), nor fulfilled by it (a single-word write lies in a cell of the stepper's
cut, `SWAt`), so both messages are new and the earlier one is `undef` (`tstep_newOrd`). -/
theorem undefLow_thread (hP : ProgT p) (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (hpA : TermPromClos.PromAllocF p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    (hpa : PromAbove (stOf r.1 r.2.1 r.2.2)) (h : UndefLowG Eg c.mem) :
    UndefLowG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c'.mem := by
  intro l cl hl o hO t1 t2 m1 m2 hlt h1 h2 hl1 hl2 hv1 hu2
  -- the stepper's typed state
  obtain ⟨S0, hRE0, -, hm0, -⟩ := X.inv.thr i th X.hth
  obtain ⟨ρ2, η2, cx2, Rf2, Rs2, hce2, hEO2, hTy2, hTv2, hF2, hRt2, -⟩ := hRE0
  have Y2 : EnvAt p Eg i th (Tot i) S0 ρ2 η2 cx2 Rf2 Rs2 :=
    ⟨hce2, congrArg TEnv.tid hce2, hEO2, hTy2, hTv2, hF2, hRt2⟩
  have hm2 : MemInv (gOf p k arch c i) (CE η2) (stOf c.mem c.pairs th) := by rw [hce2]; exact hm0
  have hFi : FInv ρ2 η2 th.σs (Resume p th.stack) cx2 th.env :=
    FInvR_FInv (hTv2.2.2.2.2.2.2.2)
      (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs2 E rd ws R h) hF2
  have hpre := tctx_pre X
  -- a new message exists only in scope
  have hnew : ∀ t (m : Msg), c.mem.size ≤ t → c'.mem[t]? = some m → StepScope cx2 th.term := by
    intro t m ht hm
    rcases hsc X Y2 with hs | hR
    · exact hs
    · have hk : r.1 = c.mem := (frame_keep hR hTy2.1 hTy2.2 hF2 hEO2 hTv2 hm2 r X.hr).1
      rw [X.e1, hk, Array.getElem?_eq_none ht] at hm; cases hm
  have hstoE : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l =
      (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto l := rfl
  by_cases hF : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
  · obtain ⟨j0, hj0, hj1, hl0⟩ := hF
    have hfl : GFreshL Eg c th l := by rw [hl0]; exact X.inv.fresh i th X.hth j0 hj0
    have hold : ∀ t (m : Msg), t < c.mem.size → c'.mem[t]? = some m → m.loc.label = l →
        c.mem[t]? = some m ∧ t ∈ th.promises := by
      intro t m ht hm hlab
      have hm' : c.mem[t]? = some m := by rw [← hpre t ht]; exact hm
      exact ⟨hm', hfl.2.2.2.2 t m hm' hlab⟩
    have hlab2 : m2.loc.label = l := by rw [hl2]
    have hlab1 : m1.loc.label = l := by rw [hl1]
    by_cases ht2 : t2 < c.mem.size
    · obtain ⟨hm2', hp2⟩ := hold t2 m2 ht2 h2 hlab2
      exact X.inv.promNU i th t2 m2 X.hth hp2 hm2' hu2
    · by_cases ht1 : t1 < c.mem.size
      · obtain ⟨hm1', hp1⟩ := hold t1 m1 ht1 h1 hlab1
        by_cases hq : t1 ∈ r.2.2.promises
        · exact (hpA X Y Z hS hPfr l ⟨j0, hj0, hj1, hl0⟩ t1 m1 hq h1).1 hlab1
        · obtain ⟨-, hful⟩ := TermFul.tstep_fulfil (fun t ht => X.inv.plt i th t X.hth ht)
            (MemInv_nopair hm2) X.hr
          obtain ⟨m, hm, hsw, -⟩ := hful t1 hp1 hq
          rw [hm1'] at hm
          cases hm
          have hs := hnew t2 m2 (Nat.le_of_not_lt ht2) h2
          have hat : TermTyped.SWAt η2 m1.loc := by
            rcases hsw with ⟨x, op, e, hterm, hw⟩ |
                ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, -, -, hb, -⟩
            · rw [hterm] at hTy2 hs
              cases hTy2.1 with
              | let_ hop _ =>
                  rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, he, -⟩ |
                      ⟨o, acq, rel, a, v, t, t', pw, nw, tr, mr, rfl, hea, -, hb, -⟩
                  · rw [he]; exact TermTyped.unitsOp_sw hop hs hFi hEO2 hTv2 hu hj
                  · exact TermTyped.fetch_sw hop hs hFi hEO2 hTv2 hm2 hea hb
            · rw [hterm] at hTy2 hs
              exact TermTyped.cas_sw hTy2.1 hs hFi hEO2 hTv2 hm2 hea hb
          obtain ⟨cl1, -, -, -, -, hcl1, -⟩ := hat
          have hc : (CE η2).sto m1.loc.label = some cl1 := hcl1
          rw [hce2, hlab1] at hc
          have hc3 := cutSto_sub hc
          rw [hfl.1] at hc3
          cases hc3
      · have hu1 := tstep_newOrd X.hr t1 t2 m1 m2 (Nat.le_of_not_lt ht1) hlt (by rw [← X.e1]; exact h1)
          (by rw [← X.e1]; exact h2) (hl1.trans hl2.symm)
        exact hv1 hu1
  · have hsto : Eg.sto l = some cl := by
      rw [hstoE, post_sto_old hF] at hl; exact hl
    by_cases ht2 : t2 < c.mem.size
    · exact h l cl hsto o hO t1 t2 m1 m2 hlt (by rw [← hpre t1 (Nat.lt_trans hlt ht2)]; exact h1)
        (by rw [← hpre t2 ht2]; exact h2) hl1 hl2 hv1 hu2
    · have hs := hnew t2 m2 (Nat.le_of_not_lt ht2) h2
      have hmt : r.1[t2]? = some m2 := by rw [← X.e1]; exact h2
      rcases tstep_newUndef hP hEO2 hTy2.1 hTv2 hFi hm2 hs X.hr hpa t2 m2 (Nat.le_of_not_lt ht2) hmt hu2 with hF2 |
          ⟨b, us, jj, ⟨c1, U, hs1, hat, hus, -⟩, htw, hloc⟩
      · rw [hl2] at hF2; exact hF hF2
      · have hb : b.label = l ∧ b.offset + jj = o ∨ b.label = l ∧ b.offset + (jj + 1) = o := by
          rcases hloc with e | e
          · obtain ⟨g1, g2⟩ := TermB5.offs_eq_mk (e.symm.trans hl2)
            exact .inl ⟨g1, g2 _ rfl⟩
          · obtain ⟨g1, g2⟩ := TermB5.offs_eq_mk (e.symm.trans hl2)
            exact .inr ⟨g1, g2 _ rfl⟩
        have hbl : b.label = l := by rcases hb with ⟨e, -⟩ | ⟨e, -⟩ <;> exact e
        have hc : (CE η2).sto b.label = some c1 := hs1
        rw [hce2, hbl] at hc
        have hc2 := cutSto_sub hc
        rw [hsto] at hc2
        cases hc2
        refine two_not_oneU hat hus htw hO ?_
        rcases hb with ⟨-, e⟩ | ⟨-, e⟩
        · exact .inl e.symm
        · exact .inr (e.symm.trans (Nat.add_assoc _ _ _).symm)

#print axioms undefLow_thread

end

/-- **`UndefLowG` across a promise step**: the promised message is an outstanding promise of the
promiser, so not `undef` (`PromNotUndef` after the step); the cells are unchanged. -/
theorem undefLow_prom {c : Cfg} {Eg Eg' : GEnv} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val}
    {w : Ts} (hsto : ∀ l, Eg'.sto l = Eg.sto l) (hnu : PromNotUndef (promise c j a v w))
    (hth : c.ths[j]? = some th) (h : UndefLowG Eg c.mem) : UndefLowG Eg' (promise c j a v w).mem := by
  obtain ⟨epc, hpj, -⟩ := promise_inv (a := a) (v := v) (w := w) hth
  have hmem : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by rw [epc]
  have hv : v ≠ .undef := by
    have h1 := hnu j _ c.mem.size ⟨a, v, w⟩ hpj (by simp) (by rw [hmem]; simp)
    exact h1
  intro l cl hl o hO t1 t2 m1 m2 hlt h1 h2 hl1 hl2 hv1
  rw [hsto] at hl
  rw [hmem] at h1 h2
  by_cases ht2 : t2 < c.mem.size
  · rw [push_lt ht2] at h2
    rw [push_lt (Nat.lt_trans hlt ht2)] at h1
    exact h l cl hl o hO t1 t2 m1 m2 hlt h1 h2 hl1 hl2 hv1
  · have ht2e : t2 = c.mem.size := by
      have := TermMem.lt_of_get h2
      simp only [Array.size_push] at this
      exact Nat.le_antisymm (Nat.lt_succ_iff.1 this) (Nat.le_of_not_lt ht2)
    subst ht2e
    simp only [Array.getElem?_push_size, Option.some.injEq] at h2
    subst h2
    exact hv

#print axioms undefLow_prom

end TermUndefLow
