import WeakCore.TermBiiS
import WeakCore.TermPlantF
import WeakCore.TermB5

/-!
# TermBiiF (BII): the promise half of `bufInitIni` (`TermPlantF.BufInitIniF`), proved

`promIniGen`'s `bufInit` branch, without the field: the fulfilling `bufInit` (from
`certified_fulfilC`, so its target is the promise's cell) is taken one more step of the tied run
(`TermBiiS.xfz_threadB`), where the certificate environment `E2` counts the written slot
(`BufInitBump`); `RunAgreeF` at that configuration bounds `E2`'s count by the planted/start one.

* `bufInit_uaIP`: the units of a typed `bufInit` are initialised in a later environment that counts
  the slot (`UnitsAtI`).
* `promIniGenB`: `promIniGen` without `hbuf`.
* `bufInitIniF_of : BufInitIniF` (the field's exact type).

Cycle guard: no `BufInitIniF`, `promIniGen`, `promNewOK_of`, `plantPromOK_of`, `pubPromOK_of` in
any proof body here (`BufInitIniF` only as `bufInitIniF_of`'s statement).
-/

namespace TermBiiF

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermGlob TermTyped TermNoHold TermMain TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- **The units of a typed `bufInit` are initialised at an extension that counts the slot**
(`TermB5.bufInit_inv`, with the handle's `IniAt` at the real count). -/
theorem bufInit_uaIP {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word} {E' : TEnv}
    (hop : OpT p cx x (.bufInit bb i v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.bufInit bb i v) pw b rel us ws)
    (hx : Ext (CE η) E')
    (hB : ∀ rt w ad rti wi n, evalAt env bb = some (rt, [w]) → w.val = .loc ad 0 →
      evalAt env i = some (rti, [wi]) → numOf [wi] = some n → n + 1 ≤ E'.ini ad.label ∧ n + 1 ≤ E'.rini ad.label) :
    UnitsAtI E' b us := by
  obtain ⟨rt, rti, wi, ad, c, N, U, jv, hea, hwv, hei, hnj, rfl, hsto, -, hini0, hat0, hjv, hacc⟩ :=
    TermB5.bufInit_inv hop hi hE htv hu
  have hel := AtOff.elem (n := N) hacc hjv (AtOff.here (Or.inl (by simp [hacc])))
  have hbump : jv + 1 ≤ E'.ini ad.label := (hB _ _ _ _ _ _ hea hwv hei hnj).1
  refine ⟨c, _, hx.2.2.2.2.1 _ _ hsto, ?_, hacc, ?_⟩
  · simpa [offs] using AtOff_trans hat0 hel
  · intro N' e hT
    rcases hini0 N' e hT with ⟨hU, hoff⟩ | ⟨us2, j2, o2, hus2, hj2, ho2, hat2⟩
    · rw [hT] at hU
      simp only [Ty.array.injEq, Idx.lit.injEq] at hU
      obtain ⟨-, rfl⟩ := hU
      refine .inr ⟨us, jv, 0, hacc, ?_, ?_, AtOff.here (Or.inl (by simp [hacc]))⟩
      · show jv < E'.ini ad.label
        omega
      · show jv * nWords us + 0 = ad.offset + jv * nWords us
        rw [← hoff]; simp
    · refine .inr ⟨us2, j2, o2 + (jv * nWords us + 0), hus2, ?_, by simp [offs]; omega, AtOff_trans hat2 hel⟩
      exact Nat.lt_of_lt_of_le hj2 (Nat.le_trans (TEnv.rc_le_ini _ _) (hx.2.2.2.2.2.1 _))

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`promIniGen` without `hbuf`**: InitR of a promise at a label shared after a promise step. The
fulfilling `bufInit` is taken one more step (`xfz_threadB`), where `RunAgreeF` bounds the count that
covers the written slot. -/
theorem promIniGenB (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0) (hbr : BufInitPubFR p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {t : Ts} {m : Msg} (htm : t ∈ th.promises ++ [c.mem.size]) (hmm : (c.mem.push ⟨a, v, w⟩)[t]? = some m)
    (cl : Cell) (hcl : Eg.sto m.loc.label = some cl)
    (hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared m.loc.label) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    InitR (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl m.loc.label m.loc.offset := by
  obtain ⟨S0, hS0⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hS0
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
  have hsc := fun c1 h1 h2 => (hrun X S0 hS0 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => (hrun X S0 hS0 c1 h1 h2).2
  obtain ⟨m', hm', c1, c2, th1, h1, h2, hc2, hth1, -, ht1, -, hsw⟩ :=
    certified_fulfilC X.cert (pwf_of_inv h0.toF.toInvAt) ht
  rw [hmt] at hm'
  cases hm'
  have hc1 : Certified p k arch c1 j := certified_back (.thread h2 (.refl _)) hc2
  have hHr : ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j → ∀ th1, c1.ths[j]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) →
        TermTyped.WitP c.mem th.promises l o τ :=
    TermTyped.witP_run X.hth hm.2.2.1 (TermCert.winInv_prom (TermCert.winInv_refl X.hth))
  obtain ⟨th1', E1, hth1', hx1, hTE1, hmi1, hSC1, hbo1, hfb1, hfr1, hna1, hfresh1, hIL1, hIH1, hPV1, hPO1⟩ :=
    solo_typedXFP (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin h0 h1 hc1 (fun l => X.inv.rle l) (hbr X S0) (hbp X) hHr
  rw [hth1] at hth1'
  cases hth1'
  have hTE1' := hTE1
  obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, -⟩ := hTE1'
  have hscope := hsc c1 h1 hc1 th1 hth1 (TermTyped.not_spawnT_of_steps hth1 h2) ρ η cx hE hT htv hi
  have e : (promise c j a v w).mem.size = c.mem.size + 1 := by rw [hpi.1, Array.size_push]
  rcases SWIni hE hT htv hi hmi1 (TermTyped.scopeD_SW hscope hsw) hsw with ⟨c', hc', hI⟩ | ⟨x, bb, i, v', e', hterm⟩
  · have hag := hagree X S0 c1 th1 (CE η) h1 hc1 hth1 hx1 hmi1 (by rw [e] at hfb1; exact hfb1) hIL1 hIH1 hPV1 hPO1
    obtain ⟨hcl0, hgle⟩ := plantIni_le (hV0 := hV0) hP hrun X hcl hsh hag hPS hSub hSig
    have hc'' : η.sto m.loc.label = some c' := hc'
    have hE1 : η.sto m.loc.label = some cl := hx1.2.2.2.2.1 _ _ hcl0
    rw [hE1] at hc''
    cases hc''
    exact fun N e us h1 h2 => Nat.lt_of_lt_of_le (hI N e us h1 h2) (Nat.mul_le_mul_right _ hgle)
  · -- the fulfilling `bufInit`, one step on
    obtain ⟨th2, E2, s, s', hth2, hF, hD, hvw, hx2, -, hm2, -, -, hfb2, -, -, -, hIL2, hIH2, hB, hx12⟩ :=
      TermBiiS.xfz_threadB (Z := IniZK Eg Tot HP j)
        (W := fun l => TermK5P.PubZ (Cut Eg j S0) (CE η) l ∨
          TermK5O.PubZO p k arch j (Cut Eg j S0) (promise c j a v w) c1 l)
        hP (hsc c1 h1 hc1)
        (TermViewInv.viewInv_solo (TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw) h1) hth1 hx1 hTE1 hmi1 hSC1 hbo1 hfb1 hfr1 hna1 hfresh1 hIL1 hIH1 h2 hc2 hPS
        (fun l hbi hz => hz.elim (hbp X c1 h1 hc1 th1 hth1 l hbi) fun hz => hz.elim
          (TermK5P.pubZ_noBufInit hPV1 (fun c1' th1' c1'' l cl g1 g2 g3 g4 g5 g6 g7 _ =>
            hbr X S0 c1' th1' c1'' c1 th1 l cl g1 g2 g3 g4 g5 hc1 hth1 g6 g7) l hbi)
          (TermK5O.pubZO_noBufInit (fun c1' th1' c1'' l cl _ g1 g2 g3 g4 g5 g6 g7 _ =>
            hbr X S0 c1' th1' c1'' c1 th1 l cl g1 g2 g3 g4 g5 hc1 hth1 g6 g7) l hbi))
        (hHr c1 h1 hc1 th1 hth1) hterm
    have hU := (hIH2 (fun l => X.inv.rle l)).2.1
    have hPV2 := TermK5P.pfrProv_thread hPV1 hF hfb1 (fun _ h => h) (fun _ h => .inr (.inl h)) hD h2 hth1 hvw hU
    have hPO2 := TermK5O.pfrProvO_thread hPO1 hF hfb1 hx1 (fun _ h => .inr (.inr h)) h2 hth1 hvw hU
    have hag := hagree X S0 c2 th2 E2 (solo_trans h1 (.thread h2 (.refl _))) hc2 hth2 hx2 hm2
      (by rw [e] at hfb2; exact hfb2) hIL2 hIH2 hPV2 hPO2
    obtain ⟨hcl0, hgle⟩ := plantIni_le (hV0 := hV0) hP hrun X hcl hsh hag hPS hSub hSig
    -- the written unit: in the slot `E2` counts
    rcases hsw with ⟨x', op, e'', ht', hw⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht', -⟩
    · rw [hterm] at ht'
      cases ht'
      rcases hw with ⟨pw, b, rel, us, ws, jw, w', hUo, hone, -, hloc, -⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, hop, -⟩
      · rw [hterm] at hT
        cases hT with
        | let_ hop _ =>
          obtain ⟨c', hc', hI⟩ := unitsAtI_initR (bufInit_uaIP hop hi hE htv hUo hx12 hB) hone
          have hE2 : E2.sto m.loc.label = some cl := hx2.2.2.2.2.1 _ _ hcl0
          rw [hloc] at hE2 hgle ⊢
          change E2.sto b.label = some cl at hE2
          rw [hE2] at hc'
          cases hc'
          exact fun N e us h1 h2 => Nat.lt_of_lt_of_le (hI N e us h1 h2) (Nat.mul_le_mul_right _ hgle)
      · cases hop
    · rw [hterm] at ht'; cases ht'

/-- **`BufInitIniF`** (the promise half of the old `bufInitIni` field), from the certificate run facts
and `RunAgreeF`; the field's own `bufInit` configuration is not used. -/
theorem bufInitIniF_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0)
    (hbr : BufInitPubFR p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    BufInitIniF p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X t m htm hmm _ _ _ _ _ _ _ _ _ _ _ _ cl hcl hsh
  exact promIniGenB (hV0 := hV0) hP hrun hagree hbp hbr X htm hmm cl hcl hsh hPS hSub hSig

end

end TermBiiF

#print axioms TermBiiF.bufInit_uaIP
#print axioms TermBiiF.promIniGenB
#print axioms TermBiiF.bufInitIniF_of
