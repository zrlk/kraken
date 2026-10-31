import WeakCore.WinStart
import WeakCore.WinScope
/-! (B11 P1/P2) The run split at a window publish and the site of a fulfilling write after it. -/
namespace FlatWinStart
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermOwnX2.Flat
  TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A promise step changes only thread `i`'s promises. -/
theorem promise_ths {c : Cfg} {i : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c.ths[i]? = some th) :
    (promise c i a v w).ths[i]? = some { th with promises := th.promises ++ [c.mem.size] } := by
  have hi : i < c.ths.size := by
    rcases Nat.lt_or_ge i c.ths.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hth; cases hth
  unfold promise; rw [hth]; simp [Array.set!, hi]

/-- **(P1) Run split at a publish**: a solo run from a thread about to publish either takes no thread step of
`i` (term and env unchanged), or reaches the publish after promise steps only. -/
theorem solo_pub_split {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c1 c1a : Cfg}
    (h : Solo p k arch i c1 c1a) : ∀ {th1 : TTh} {y : String} {a : At} {e : Expr},
    c1.ths[i]? = some th1 → th1.term = .let_ y (.publish a) e →
    (∃ tha, c1a.ths[i]? = some tha ∧ tha.term = th1.term ∧ tha.env = th1.env) ∨
    ∃ c1p thp c1', Solo p k arch i c1 c1p ∧ c1p.ths[i]? = some thp ∧ thp.term = th1.term ∧
      thp.env = th1.env ∧ c1' ∈ threadSteps p k arch c1p i ∧ Solo p k arch i c1' c1a := by
  induction h with
  | refl c => intro th1 _ _ _ hth _; exact Or.inl ⟨th1, hth, rfl, rfl⟩
  | thread hs hrest _ =>
      intro th1 _ _ _ hth _
      exact Or.inr ⟨_, th1, _, .refl _, hth, rfl, rfl, hs, hrest⟩
  | prom a' v w hw hrest ih =>
      intro th1 y a e hth hterm
      rcases ih (promise_ths hth) hterm with ⟨tha, h1, h2, h3⟩ | ⟨c1p, thp, c1', h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl ⟨tha, h1, h2, h3⟩
      · exact Or.inr ⟨c1p, thp, c1', .prom a' v w hw h1, h2, h3, h4, h5, h6⟩
  | ext hs hrest _ =>
      intro th1 y a e hth hterm
      exfalso
      obtain ⟨th', x, n, a', e', -, -, -, hth', ht', -⟩ := extSteps_elim hs
      rw [hth] at hth'; cases hth'; rw [hterm] at ht'; cases ht'

/-- **(P2) The site of a fulfilling write at count 0**: a thread step from `c` (♭ `OwnXLeB … 0`) that fulfils
an own promise `t` at label `x` writes an initialised unit of the lineage env `E`, which is `InitRr`, or
above `E`'s frontier, or seen. -/
theorem fulfil_siteB [WrIniCB] {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel}
    {c c' : Cfg} {th : TTh} {t : Ts} {m : Msg}
    (hth : c.ths[i]? = some th) (hsc : ScopeAtB p i c) (hvI : TermViewInv.ViewInv c)
    (hI : OwnXLeB p k arch E0 i x 0 c) (hs : c' ∈ threadSteps p k arch c i)
    (ht : t ∈ th.promises) (hn : t ∉ TermFul.promsOf c' i) (hm : c.mem[t]? = some m) (hl : m.loc.label = x) :
    ∃ E, MemInvB (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧ ExtB E0 E ∧
      E.rini x ≤ E0.rini x ∧ E.ini x ≤ max (E0.ini x) (E0.rini x) ∧
      ∃ cl, E.sto x = some cl ∧ InitR E cl x m.loc.offset ∧
        (InitRr E cl x m.loc.offset ∨ (∀ f, E.pfr x = some f → f < t) ∨ E.seen x) := by
  obtain ⟨th1, E, Tot, HP, hth1, ⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, hFI, hsum, hRP, -⟩, hmi, hH, hbf, hnie,
    hsto, hle, hx0, hA, -, -, hZ, -⟩ := hI
  rw [hth] at hth1
  cases hth1
  subst hCE
  have h3 := congrArg (fun R : Res => R (.own x)) hsum
  simp only [Res.add_apply] at h3
  have h0 : Rf (.own x) = 0 := by omega
  have hFp := TermOwnX2.Flat.finv_ofB htv hFI
  have hscD := hsc th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT.1 htv hFp
  have hvr := TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI (.refl _) hth
  obtain ⟨th', r, hth', hr, e1, e2, e3, -⟩ := threadSteps_inv hs
  rw [hth] at hth'
  cases hth'
  have hW := WrIniCB.wrA hE hT.1 htv hFp hmi hscD hvr hr
  have hn' : t ∉ r.2.2.promises := by rwa [promsOf_some e3] at hn
  have hrm : r.1[t]? = some m := (tstep_grow hr).1 t m hm
  refine ⟨CE η, hmi, hx0, hZ rfl, ?_, ?_⟩
  · have h1 := hA.1 x hsto
    have h2 := hZ rfl
    omega
  rcases hW t m hn' hrm with ⟨hnp, -⟩ | hfr | ⟨cl, hcl, hIR, hor⟩ |
      ⟨x1, bb, ib, v, e, hterm, rt, w, ad, rti, wi, n, cl, hbb, hw, -, -, hadl, -, -⟩
  · exact absurd ht hnp
  · exfalso
    obtain ⟨j, hj, -, hjl⟩ := hfr
    have := (hmi.2.2.2.1.1 j hj).1
    rw [← hjl, hl] at this
    exact hsto this
  · rw [hl] at hcl hIR hor
    refine ⟨cl, hcl, hIR, ?_⟩
    rcases hor with h | h | h | h
    · exact Or.inl h
    · exfalso
      have := hmi.2.2.1 t ht
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le this h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exfalso
    exact not_bufInitL_ofB hE hT.1 hFI h0
      ⟨x1, bb, ib, v, e, rt, [w], ad, hterm, hbb, by simp [hw], hadl.trans hl⟩

/-- **(P1+P2) A promise outstanding at a certified window publish of `x`, at a unit of `x`, is fulfilled after
the shadow publish at an initialised unit of a count-0 lineage env `E`, bounded at `x` by the publish-point
typing `η1`**; that unit is `InitRr`, or above `E`'s frontier, or `x` is seen at `E`. -/
theorem pub_fulfil [WrIniCB] {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {k : Promises.Knobs}
    {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {c c1 : Cfg} {th1 : TTh} {y : String} {a : At} {e : Expr}
    {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat} {t : Ts} {m : Msg}
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAtB p i c0) (hvI : TermViewInv.ViewInv c)
    (h0 : OwnXLeB p k arch E0 i x 1 c) (hTA : TermTyped.TidAt i c E0) (hR0 : ∀ l, E0.rini l ≤ E0.ini l)
    (h1 : Solo p k arch i c c1) (hc1 : Certified p k arch c1 i) (hpw : PWF c1 i)
    (hth : c1.ths[i]? = some th1) (hterm : th1.term = .let_ y (.publish a) e)
    (hea : evalAt th1.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad g']) (hx : ad.label = x)
    (ht : t ∈ th1.promises) (hm : c1.mem[t]? = some m) (hl : m.loc.label = x) :
    ∃ c1p thp η1, Solo p k arch i c c1p ∧ c1p.ths[i]? = some thp ∧ EnvOKB p η1 ∧
      MemInvB (gOf p k arch c1p i) (CE η1) (stOf c1p.mem c1p.pairs thp) ∧ ExtB E0 (CE η1) ∧
      (CE η1).sto x ≠ none ∧ (∀ l, (CE η1).rini l ≤ (CE η1).ini l) ∧
      ∃ E, ExtB (reAncB E0 (CE η1) x) E ∧ E.rini x ≤ (CE η1).rini x ∧ E.ini x ≤ (CE η1).ini x ∧
        ∃ cl, E.sto x = some cl ∧ InitR E cl x m.loc.offset ∧
          (InitRr E cl x m.loc.offset ∨ (∀ f, E.pfr x = some f → f < t) ∨ E.seen x) := by
  obtain ⟨c', hs, hnp⟩ := hc1
  have hn' : t ∉ TermFul.promsOf c' i := by rw [noPromises_nil hnp]; exact List.not_mem_nil
  obtain ⟨m', hm', c1a, c2, th1a, hs1, hst, hs4, hth1a, hm1a, ht1a, hn2, -, -, -⟩ :=
    solo_fulfil hs hpw t (by rw [promsOf_some hth]; exact ht) hn'
  rw [hm] at hm'
  cases hm'
  have hc1a : Certified p k arch c1a i := ⟨c', .thread hst hs4, hnp⟩
  rcases solo_pub_split hs1 hth hterm with ⟨tha, ha1, ha2, -⟩ | ⟨c1p, thp, c1', hp1, hp2, hp3, hp4, hp5, hp6⟩
  · exfalso
    rw [hth1a] at ha1
    cases ha1
    obtain ⟨th', r, hth', hr, -, -, e3, -⟩ := threadSteps_inv hst
    rw [hth1a] at hth'
    cases hth'
    have hpr := (tstep_publish_relSt (ha2.trans hterm) hr).2.1
    rw [promsOf_some e3, hpr] at hn2
    exact hn2 ht1a
  · obtain ⟨η1, hE1, hm1, hX1, hs1', hr1, hI⟩ :=
      ownXLe_pub_chainS hP hPS hSub hSig hQ hvI h0 hTA (solo_trans h1 hp1) hp5 hp2 (hp3.trans hterm)
        (by rw [hp4]; exact hea) hws hx hp6 hc1a hR0
    have hsolo : Solo p k arch i c c1a := solo_trans h1 hs1
    obtain ⟨E, -, hXE, hrE, hiE, cl, hcl, hIR, hor⟩ :=
      fulfil_siteB hth1a (hQ c1a hsolo hc1a) (TermViewInv.viewInv_solo hvI hsolo) hI hst ht1a hn2 hm1a hl
    simp only [reAncB, if_pos] at hrE hiE
    refine ⟨c1p, thp, η1, solo_trans h1 hp1, hp2, hE1, hm1, hX1, hs1', hr1, E, hXE, hrE, ?_, cl, hcl, hIR, hor⟩
    have := hr1 x
    exact Nat.le_trans hiE (Nat.max_le.2 ⟨Nat.le_refl _, this⟩)

end FlatWinStart
