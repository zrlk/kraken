import WeakCore.TermPlantF

/-! # TermPromClos: `plantClos` (`PubClosT`) from the `SysInvN` clause `promClos`

`TermMain.PromClosG` (an outstanding promise at a `noOwnIn`/`rgnFree` cell naming an own cell of
its promiser names a cell with a frontier) is kept by every step:
- a promise step fires `plantOf` along the new promise's own `PlantR` edge (`promClos_prom`);
- a thread step keeps cells, owners and frontiers away from its fresh labels, and at a fresh
  label `PromAllocF` (the named run fact, per allocation event) rules out an outstanding promise
  naming it or lying at it (`promClos_thread`).
`PubClosT` then reads the clause at the step's pre-state: the newly shared cell is one of the
stepper's (`GFoot`), of a `noOwnIn`/`rgnFree` type (`PubCpl E'`), so `pubClosT_of`. -/

namespace TermPromClos
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermMain TermInterf TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- (named, explorer-probed: the B2, pa2) **At an allocation no outstanding promise of the allocator
lies at the new label, nor names it from a cell of a `noOwnIn`/`rgnFree` type**: a thread step's
fresh label is not the location of any promise the stepper still has outstanding after the step,
nor the pointer value of one at such a cell of the step's environment `E'` (when the new label is a
cell of `E'`).  (A relaxed promise naming a future fresh label at an
`own`-typed cell does survive the allocation on ARM, the pa2/a1: hence the type premise.) -/
def PromAllocF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ L, FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc L → ∀ (t : Ts) (m : Msg), t ∈ r.2.2.promises →
      c'.mem[t]? = some m → m.loc.label ≠ L ∧ ∀ (a' : Address) (g : Nat), m.val = .loc a' g →
        ∀ cm, E'.sto m.loc.label = some cm → Ty.noOwnIn [] cm.ty = true → rgnFree cm.ty = true →
        ∀ cl, E'.sto a'.label = some cl → a'.label ≠ L

/-- Frontiers survive a step of `E_g`. -/
theorem gfoot_pfr {g : G} {Eg Eg2 : GEnv} {n n' : Nat} {v : Ts} (hf : GFoot g Eg Eg2 n n' v)
    {l : AllocLabel} {f : Ts} (h : Eg.pfr l = some f) : Eg2.pfr l = some f := by
  rcases hf.2.2.2.2.1 l with e | ⟨e, -⟩ | ⟨-, e, -⟩
  · rw [e]; exact h
  · rw [e] at h; cases h
  · rw [e] at h; cases h

/-- **No thread has an outstanding promise at another (existing) thread's private cell**:
`PromsOK` puts it among the owner's ghost foreign promises (`PromsDisj`), which are `Vis`ible
(`FpOK`). -/
theorem foreign_priv {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hI : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) {i q : Nat} {thi thq : TTh}
    (hi : c.ths[i]? = some thi) (hq : c.ths[q]? = some thq) (hiq : i ≠ q) {t : Ts} (ht : t ∈ thi.promises)
    {m : Msg} (hm : c.mem[t]? = some m) {cm : Cell} (hs : Eg.sto m.loc.label = some cm)
    (ho : cm.owner = some q) (hp : Eg.pfr m.loc.label = none) : False := by
  have hA : t ∈ allProms c := TermStepper.mem_allProms.2 ⟨i, thi, hi, ht⟩
  rcases List.mem_append.1 ((hI.proms q thq hq t).2 hA) with h2 | h2
  · exact hI.disj i q thi thq t hiq hi hq ht h2
  · exact (hI.fpok q thq (fun _ => False) hq).2 t m h2 hm ⟨⟨cm, cutSto_own hs ho, ho⟩, hp⟩

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **A thread step keeps `promClos`.** -/
theorem promClos_thread (hA : PromAllocF p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E') :
    PromClosG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' := by
  intro j thj t m hj ht hm a' g hv cl hcl ho cm hcm hin hno hrf
  have hgf := gfoot_of X Y Z
  have hCut := tctx_cut X Y Z
  obtain ⟨th0, h0, hs, hi, -⟩ := tctx_old X hj
  have ht0 : t ∈ th0.promises := hs t ht
  have hlt : t < c.mem.size := X.inv.plt j th0 t h0 ht0
  have hm0 : c.mem[t]? = some m := by rw [← tctx_pre X t hlt]; exact hm
  have hcm0 : Eg.sto m.loc.label = some cm := by
    have h2 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto m.loc.label = some cm := hcm
    rcases hgf.2.1 m.loc.label with e | ⟨hF, -, -, -, -⟩
    · rw [e] at h2; exact h2
    · exfalso
      by_cases hji : j = i
      · subst hji
        obtain ⟨-, e3⟩ := hi rfl
        subst e3
        exact (hA X Y Z hS hPfr _ hF t m ht hm).1 rfl
      · obtain ⟨n, hn, -, e⟩ := hF
        have hti : t ∈ th.promises := (X.inv.fresh i th X.hth n hn).2.2.2.2 t m hm0 e
        exact X.inv.disj i j th th0 t (Ne.symm hji) X.hth h0 hti ht0
  have hcl0 : Eg.sto a'.label = some cl := by
    have h2 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto a'.label = some cl := hcl
    rcases hgf.2.1 a'.label with e | ⟨hF, -, -, T, hT⟩
    · rw [e] at h2; exact h2
    · rw [hT] at h2
      cases h2
      have hji : j = i := Option.some.inj ho.symm
      subst hji
      obtain ⟨-, e3⟩ := hi rfl
      subst e3
      have hEm : E'.sto m.loc.label = some cm := by
        have h3 : (Cut (EgT Eg (gOf p k arch c j) th.nalloc r.2.2.nalloc E' c') j E'.seen).sto m.loc.label =
            some cm := by
          rcases hin with h4 | h4
          · exact cutSto_own hcm h4
          · exact cutSto_shared hcm h4
        rw [hCut] at h3; exact h3
      have hEl : E'.sto a'.label = some ⟨T, some j⟩ := by
        have h3 : (Cut (EgT Eg (gOf p k arch c j) th.nalloc r.2.2.nalloc E' c') j E'.seen).sto a'.label =
            some ⟨T, some j⟩ := cutSto_own hcl ho
        rw [hCut] at h3; exact h3
      exact absurd rfl ((hA X Y Z hS hPfr _ hF t m ht hm).2 a' g hv cm hEm hno hrf _ hEl)
  have hin0 : cm.owner = some j ∨ Eg.Shared m.loc.label := by
    rcases hin with h4 | ⟨f4, hf4⟩
    · exact .inl h4
    · rcases hgf.2.2.2.2.1 m.loc.label with e | ⟨hp0, -, -, -, cq, hcq, hoq⟩ | ⟨-, -, e⟩
      · exact .inr ⟨f4, e ▸ hf4⟩
      · rw [hcm0] at hcq
        cases hcq
        by_cases hji : j = i
        · subst hji; exact .inl hoq
        · exact (foreign_priv X.inv h0 X.hth hji ht0 hm0 hcm0 hoq hp0).elim
      · have h2 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto m.loc.label = some cm := hcm
        rw [e] at h2; cases h2
  obtain ⟨f, hf⟩ := X.inv.promClos j th0 t m h0 ht0 hm0 a' g hv cl hcl0 ho cm hcm0 hin0 hno hrf
  exact ⟨f, gfoot_pfr hgf hf⟩

/-- **A promise step keeps `promClos`**: the new promise's own `PlantR` edge plants its target. -/
theorem promClos_prom (hpl : PromLocF p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) :
    PromClosG (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w) := by
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hpfr : ∀ l f, Eg.pfr l = some f →
      ∃ f', (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).pfr l = some f' := by
    intro l f h
    simp only [EgP, GEnv.withFp, plantG]
    cases e : plantOf c Eg j a v w l with
    | none => exact ⟨f, h⟩
    | some f' => exact ⟨f', rfl⟩
  have hold : ∀ (i : Nat) (thi : TTh) (t : Ts) (m : Msg), c.ths[i]? = some thi → t ∈ thi.promises →
      (promise c j a v w).mem[t]? = some m → c.mem[t]? = some m := by
    intro i thi t m hi ht hm0
    have hlt : t < c.mem.size := X.inv.plt i thi t hi ht
    have hm : (c.mem.push ⟨a, v, w⟩)[t]? = some m := by rw [hpi.1] at hm0; exact hm0
    rw [Array.getElem?_push_lt hlt] at hm
    rw [Array.getElem?_eq_getElem hlt]
    exact hm
  intro i thi t m hi ht hm a' g hv cl hcl ho cm hcm hin hno hrf
  have hcl0 : Eg.sto a'.label = some cl := hcl
  have hcm0 : Eg.sto m.loc.label = some cm := hcm
  have hin0 : ∀ thi', c.ths[i]? = some thi' → t ∈ thi'.promises → c.mem[t]? = some m →
      cm.owner = some i ∨ Eg.Shared m.loc.label := by
    intro thi' hi' ht' hm'
    rcases hin with h4 | ⟨f4, hf4⟩
    · exact .inl h4
    · cases hq : Eg.pfr m.loc.label with
      | some f5 => exact .inr ⟨f5, hq⟩
      | none =>
        have hf5 : plantOf c Eg j a v w m.loc.label = some f4 := by
          revert hf4
          simp only [EgP, GEnv.withFp, plantG, hq]
          cases plantOf c Eg j a v w m.loc.label with
          | none => intro e; cases e
          | some f6 => intro e; simpa using e
        obtain ⟨⟨l1, -, t1, -, m1, -, -, -, a1, g1, -, -, cq, hcq, hoq, -⟩, -⟩ := plantOf_some X.hth hf5
        rw [cutSto_sub (Eg := Eg) (i := j) hcq] at hcm0
        cases hcm0
        by_cases hij : i = j
        · subst hij; exact .inl hoq
        · exact (foreign_priv X.inv hi' X.hth hij ht' hm' hcm hoq hq).elim
  by_cases hij : i = j
  · subst hij
    rw [hpi.2.1] at hi
    cases hi
    rcases List.mem_append.1 ht with ht | ht
    · obtain ⟨f, hf⟩ := X.inv.promClos i th t m X.hth ht (hold i th t m X.hth ht hm) a' g hv cl hcl0 ho cm hcm0
        (hin0 th X.hth ht (hold i th t m X.hth ht hm)) hno hrf
      exact hpfr _ f hf
    · rw [List.mem_singleton] at ht
      subst ht
      have hm2 : (c.mem.push ⟨a, v, w⟩)[c.mem.size]? = some m := by rw [hpi.1] at hm; exact hm
      rw [Array.getElem?_push_size] at hm2
      cases hm2
      cases hq : Eg.pfr a'.label with
      | some f => exact hpfr _ f hq
      | none =>
        have hcutA : cutSto Eg i a.label = some cm := by
          rcases hpl X with ⟨cl0, hc0⟩ | ⟨n, hn, e⟩
          · have e2 := cutSto_sub hc0
            rw [hcm0] at e2
            cases e2
            exact hc0
          · have h1 := (X.inv.fresh i th X.hth n hn).1
            rw [← e] at h1
            rw [h1] at hcm0
            cases hcm0
        have hR : TermTyped.PlantR (cutP Eg i) (c.mem.push ⟨a, v, w⟩) (th.promises ++ [c.mem.size]) a.label a'.label :=
          ⟨c.mem.size, List.mem_append_right _ (List.mem_singleton_self _), ⟨a, v, w⟩, Array.getElem?_push_size,
            rfl, ⟨cm, hcutA, hno, hrf⟩, a', g, hv, rfl, cl, cutSto_own hcl0 ho, ho, hq⟩
        have hpo := plantOf_of (Eg := Eg) (a := a) (v := v) (w := w) (l := a'.label) X.hth ⟨a.label, ClR.base, hR⟩
        refine ⟨plantF (cutP Eg i) (stOf c.mem c.pairs th) a'.label, ?_⟩
        simp only [EgP, GEnv.withFp, plantG, hpo]
  · have hi' : c.ths[i]? = some thi := by rw [← TermStepper.promise_other X.hth hij]; exact hi
    obtain ⟨f, hf⟩ := X.inv.promClos i thi t m hi' ht (hold i thi t m hi' ht hm) a' g hv cl hcl0 ho cm hcm0
      (hin0 thi hi' ht (hold i thi t m hi' ht hm)) hno hrf
    exact hpfr _ f hf

/-- **The former field `plantClos`** (`PubClosT`) from the `SysInvN` clause `promClos` and
`PromAllocF`. -/
theorem pubClosT_of (hA : PromAllocF p k arch Sp Init MintOK c0) : PubClosT p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hS hPfr l f hl0 hl1 t m ht hm hml
    a' g hv cl hcl ho
  have hgf := gfoot_of X Y Z
  have hCut := tctx_cut X Y Z
  have ht0 : t ∈ th.promises := tctx_sub X t ht
  have hlt : t < c.mem.size := X.inv.plt i th t X.hth ht0
  have hm0 : c.mem[t]? = some m := by rw [← tctx_pre X t hlt]; exact hm
  have hcl2 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto a'.label = some cl := by
    have h : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen).sto a'.label = some cl := by
      rw [hCut]; exact hcl
    exact cutSto_sub h
  have hcm : ∃ cm, Eg.sto l = some cm ∧ cm.owner = some i ∧ E'.sto l = some cm := by
    rcases hgf.2.2.2.2.1 l with e | ⟨-, f1, -, -, hO⟩ | ⟨hF, -⟩
    · have e2 : E'.pfr l = Eg.pfr l := e
      rw [e2, hl0] at hl1
      cases hl1
    · obtain ⟨cm, hcm, hown⟩ := hO
      have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hF => by
        rw [(X.inv.gfresh X.hth r.2.2.nalloc l hF).1] at hcm; cases hcm
      have h2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cm :=
        (hgf.sto_old hnF).trans hcm
      have h3 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen).sto l = some cm :=
        cutSto_own h2 hown
      rw [hCut] at h3
      exact ⟨cm, hcm, hown, h3⟩
    · exact absurd hml ((hA X Y Z hS hPfr l hF t m ht hm).1)
  obtain ⟨cm, hcm0, hcmo, hcm1⟩ := hcm
  obtain ⟨-, -, -, hno, hrf⟩ := Z.2.2.1.2.2.2.2.2.2.2.2.1.2.2.1 l cm f hcm1 hl1
  have hcl0 : Eg.sto a'.label = some cl := by
    rcases hgf.2.1 a'.label with e | ⟨hF, -⟩
    · rw [e] at hcl2; exact hcl2
    · exact absurd rfl ((hA X Y Z hS hPfr _ hF t m ht hm).2 a' g hv cm (by rw [hml]; exact hcm1) hno hrf cl hcl)
  obtain ⟨f', hf'⟩ := X.inv.promClos i th t m X.hth ht0 hm0 a' g hv cl hcl0 ho cm (by rw [hml]; exact hcm0)
    (.inl hcmo) hno hrf
  exact ⟨f', gfoot_pfr hgf hf'⟩

end

end TermPromClos

#print axioms TermPromClos.gfoot_pfr
#print axioms TermPromClos.foreign_priv
#print axioms TermPromClos.promClos_thread
#print axioms TermPromClos.promClos_prom
#print axioms TermPromClos.pubClosT_of
