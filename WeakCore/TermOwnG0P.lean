import WeakCore.TermOwnG0

/-!
# TermOwnG0P: discharge of `PfrX` through the ghost `G.pf` (EFoot tags)

`solo_typedXRP` is the typed run `solo_typedXR` restricted to `SoloNP r`, tracking `pfr r = none`.
At each thread step the footprint is taken at `g′ = {gOf … with pf := (· ≠ r)}`
(`TermPf`: `tstep`, `MemInv`, `PAx`, `boxFence` are inert in `pf`). The footprint's `PfrG` then
forbids a frontier change at `r`. The only `pf` premise of `tstep_footprint` is the tag-0 `hPb`,
which `SoloNP`'s guard `¬ PubAt th r` supplies.

`PfrX_of` gives `PfrX` from a start witness with `pfr r = none` (`h0P`).  `g0WinT_ofP` /
`g0Win_ofP` are `g0WinT_of` / `g0Win_of` with `PfrX` discharged and the unused premises pruned
(B2 (a)); `TermOwnG0` is left unchanged.

Copies to replace with core exports later:
* `invAtXRB_prom`: COPY of `TermTyped.InvAtXR_prom`, keeping the environment.
* `solo_typedXRP`: COPY of `TermTyped.solo_typedXR`, over `SoloNP r` with `pfr r = none`.
-/

namespace TermOwnG0
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermOwnG0Defs TermOwnG0W
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {r : AllocLabel}

theorem soloNP_trans {c c' c'' : Cfg} (h1 : SoloNP p k arch i r c c') (h2 : SoloNP p k arch i r c' c'') :
    SoloNP p k arch i r c c'' := by
  induction h1 with
  | refl => exact h2
  | thread hs hn _ ih => exact .thread hs hn (ih h2)
  | prom a v w hw _ ih => exact .prom a v w hw (ih h2)
  | ext hs _ ih => exact .ext hs (ih h2)

/-- `run_inv` over `SoloNP r`: the thread step carries the guard `¬ PubAt th r`. -/
theorem runNP_inv {c1 : Cfg} {P : Cfg → Prop}
    (hstep : ∀ c0 c0', P c0 → c0' ∈ threadSteps p k arch c0 i → (∀ th, c0.ths[i]? = some th → ¬ PubAt th r) →
      SoloNP p k arch i r c0' c1 → P c0')
    (hprom : ∀ c0 a v w, P c0 → w < c0.mem.size → SoloNP p k arch i r (promise c0 i a v w) c1 →
      P (promise c0 i a v w))
    (hext : ∀ c0 c0', P c0 → c0' ∈ extSteps c0 i → SoloNP p k arch i r c0' c1 → P c0')
    {c c2 : Cfg} (h : SoloNP p k arch i r c c2) (h2 : SoloNP p k arch i r c2 c1) (h0 : P c) : P c2 := by
  revert h0 h2
  induction h with
  | refl => exact fun _ h0 => h0
  | thread hs hn hrest ih => exact fun h2 h0 => ih h2 (hstep _ _ h0 hs hn (soloNP_trans hrest h2))
  | prom a v w hw hrest ih => exact fun h2 h0 => ih h2 (hprom _ a v w h0 hw (soloNP_trans hrest h2))
  | ext hs hrest ih => exact fun h2 h0 => ih h2 (hext _ _ h0 hs (soloNP_trans hrest h2))

-- COPY of TermTyped.InvAtXR_prom
theorem invAtXRB_prom {E0 : TEnv} {n0 v0 : Nat} {mem0 : Memory} {P0 : List Ts} {l : AllocLabel} {cl : Cell}
    {c0 : Cfg} {th : TTh} {E : TEnv} {a : Address} {v : WeakMem.Val} {w : Ts} (hth : c0.ths[i]? = some th)
    (h : InvAtXRB p k arch i E0 n0 v0 mem0 P0 l cl c0 th E) :
    ∃ th', (promise c0 i a v w).ths[i]? = some th' ∧
      InvAtXRB p k arch i E0 n0 v0 mem0 P0 l cl (promise c0 i a v w) th' E := by
  obtain ⟨hx, hTE, hm, hSC, hbo, hfb, hfr, hrh⟩ := h
  refine ⟨_, (promise_inv (a := a) (v := v) (w := w) hth).2.1, hx, hTE, ?_, hSC,
    by rw [gOf_promise]; exact hbo, hfb, ?_, hrh⟩
  · rw [gOf_promise, (promise_inv (a := a) (v := v) (w := w) hth).2.2]
    exact MemInv_promSt hm
  · exact frRunA_prom hth hfr

/-- (IO1) An extern move keeps `InvAtXRB` (environment and `vWr` unchanged). -/
theorem invAtXRB_ext {E0 : TEnv} {n0 v0 : Nat} {mem0 : Memory} {P0 : List Ts} {l : AllocLabel} {cl : Cell}
    {c0 c0' : Cfg} {th : TTh} {E : TEnv} (hth : c0.ths[i]? = some th)
    (h : InvAtXRB p k arch i E0 n0 v0 mem0 P0 l cl c0 th E) (hs : c0' ∈ extSteps c0 i) :
    ∃ th', c0'.ths[i]? = some th' ∧ InvAtXRB p k arch i E0 n0 v0 mem0 P0 l cl c0' th' E := by
  obtain ⟨hx, hTE, hm, hSC, hbo, hfb, hfr, hrh⟩ := h
  obtain ⟨x1, a1, e1, evs, hterm, rfl⟩ := extSteps_thread hs hth
  exact ⟨_, set_self hth, hx, TermTyped.ThInvE_emit hterm hTE, by rw [gOf_ext hs]; exact hm, hSC,
    by rw [gOf_ext hs]; exact hbo, hfb, hfr, hrh⟩

-- COPY of TermTyped.solo_typedXR
/-- **The typed run before `publish r`, with the unplanted frontier**: along `SoloNP r` from `c`,
the tracked `InvAtXR` witness keeps `pfr r = none`. -/
theorem solo_typedXRP {cP c : Cfg} {E0 : TEnv} {n0 v0 : Nat} {thP : TTh} {l : AllocLabel} {cl cr : Cell}
    [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (hthP : cP.ths[i]? = some thP) (hpl : ∀ t, t ∈ thP.promises → t < cP.mem.size)
    (hcl : E0.sto l = some cl) (hcr : E0.sto r = some cr) (hW : WinInv cP i c)
    (h0 : ∃ th E, c.ths[i]? = some th ∧ InvAtXRB p k arch i E0 n0 v0 cP.mem thP.promises l cl c th E ∧
      E.pfr r = none)
    {c2 : Cfg} (h : SoloNP p k arch i r c c2) (hc2 : Certified p k arch c2 i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ th E, c2.ths[i]? = some th ∧ InvAtXRB p k arch i E0 n0 v0 cP.mem thP.promises l cl c2 th E ∧
      E.pfr r = none := by
  refine (runNP_inv (c1 := c2)
    (P := fun c0 => SoloNP p k arch i r c c0 ∧ ∃ th E, c0.ths[i]? = some th ∧
      InvAtXRB p k arch i E0 n0 v0 cP.mem thP.promises l cl c0 th E ∧ E.pfr r = none) ?_ ?_ ?_ h
    (.refl _) ⟨.refl _, h0⟩).2
  · rintro c0 c0' ⟨hc0N, th, E, hth, ⟨hx, hTE, hm, hSC, hbo, hfb, hfr, hrh⟩, hpf0⟩ hs hnp hrest
    have hc0 := hc0N.toSolo
    have hc0' : Certified p k arch c0' i := certified_back hrest.toSolo hc2
    have hcert0 : Certified p k arch c0 i := certified_back (.thread hs hrest.toSolo) hc2
    obtain ⟨th', rs, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc0'
    rw [hth] at hth'
    cases hth'
    obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp⟩ := hTE
    have hscope := hsc c0 hc0 hcert0 th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT htv hi
    -- No plant builder (EFoot_plant / plantSet / plantE) is reachable from thread steps;
    -- at g′ = {gOf … with pf := (· ≠ r)} the footprint needs only `hPb`, from `¬ PubAt th r`.
    obtain ⟨-, hstep⟩ := tstep_footprintQ (hRP := hrp) (hPS := hPS) (hSub := hSub) (hSig := hSig) (g := { gOf p k arch c0 i with pf := fun l' => l' ≠ r }) hP rfl
      (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)))
      (tstep_notDone hr) hscope hT hi hE htv hm hbo (PAx_of_step hs hc0' hth)
      (hwin c0 hc0 hcert0 th hth ρ η cx hE hT htv hi hm (frRunA_ext hfr hx) hfr.2.1.1 hfr.2.1.2.2.1)
      (hPb := fun y a e rt ws ad ht hea hws hEq => hnp th hth ⟨y, a, e, rt, ws, ad, ht, hea, hws, hEq⟩)
    obtain ⟨E', hF, hx', hT', hm', hbB⟩ := hstep rs hr hpa
    have hA' := anchR_tstep hF hm' hbB hE hT htv hi hm hscope (TermViewInv.envVR_solo hvI hc0 hth) hr (frRunA_ext hfr hx) hfr.2.1
    have hcrE : (CE η).sto r ≠ none := by rw [hx.2.2.2.2.1 _ _ hcr]; exact fun h => by cases h
    have hpf' : E'.pfr r = none := Classical.byContradiction fun hne => by
      have h3 : r ≠ r := hF.1.pfrG r hcrE (by rw [hpf0]; exact hne)
      exact h3 rfl
    have hwu := tstep_wrUp _ _ _ _ rs hr
    have hfb' := FrBound_foot hF hwu hfb hfr.1
    have hW0 := solo_winInv hc0 hW
    refine ⟨soloNP_trans hc0N (.thread hs hnp (.refl _)), rs.2.2, E', e3, ⟨Ext_trans hx hx', hT', ?_,
      StoClo_EFoot hF.1 hSC, by rw [gOf_thread hs]; exact hbo, hfb'.1, ?_, ?_⟩, hpf'⟩
    · rw [gOf_thread hs, e1, e2]
      exact hm'
    · rw [e1, e2]
      exact ⟨hfb'.2, hA', hfr.2.2⟩
    · intro N e us hT0 hus o ho hno
      by_cases hlt : o < (CE η).rini l * nWords us
      · obtain ⟨τ, h1, h2⟩ := hrh N e us hT0 hus o hlt hno
        exact ⟨τ, Nat.le_trans h1 hwu.1, h2⟩
      · obtain ⟨τ, hτ, hτ'⟩ := hF.1.riniW l cl (hx.2.2.2.2.1 _ _ hcl) N e us hT0 hus o (Nat.le_of_not_lt hlt) ho
        obtain ⟨thW0, thW, hW0P, hW0t, -, hme, hpr, -, -⟩ := hW0
        rw [hthP] at hW0P; cases hW0P
        rw [hth] at hW0t; cases hW0t
        have hsz := TermFul.memExt_size hme
        refine ⟨τ, hτ, ?_⟩
        rcases hτ' with h | ⟨hu, m, hm1, hl⟩
        · exact Or.inl (Nat.le_trans hsz h)
        · rcases hpr τ hu with h | h
          · have hlt0 := hpl τ h
            have hm0 : cP.mem[τ]? = some cP.mem[τ] := by simp [hlt0]
            have e' : c0.mem[τ]? = some m := hm1
            rw [hme τ _ hm0] at e'
            cases e'
            exact Or.inr ⟨h, _, hm0, hl⟩
          · exact Or.inl h
  · rintro c0 a v w ⟨hc0N, th, E, hth, hB, hpf0⟩ hw _
    obtain ⟨th', hth', hB'⟩ := invAtXRB_prom (a := a) (v := v) (w := w) hth hB
    exact ⟨soloNP_trans hc0N (.prom a v w hw (.refl _)), th', E, hth', hB', hpf0⟩
  · rintro c0 c0' ⟨hc0N, th, E, hth, hB, hpf0⟩ hs _
    obtain ⟨th', hth', hB'⟩ := invAtXRB_ext hth hB hs
    exact ⟨soloNP_trans hc0N (.ext hs (.refl _)), th', E, hth', hB', hpf0⟩

/-- **`PfrX` discharged**: from a start witness at the plant with no frontier at `r`. -/
theorem PfrX_of {cP : Cfg} {thP : TTh} {a0 : Address} {v0 : WeakMem.Val} {w : Ts} {E0 : TEnv} {n0 vw : Nat}
    {l : AllocLabel} {cl cr : Cell} [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i (promise cP i a0 v0 w) c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv (promise cP i a0 v0 w))
    (hwin : ∀ c0, Solo p k arch i (promise cP i a0 v0 w) c0 → Certified p k arch c0 i →
      NoHoldPubA p k arch E0 E0 i c0)
    (hthP : cP.ths[i]? = some thP) (hpl : ∀ t, t ∈ thP.promises → t < cP.mem.size)
    (hcl : E0.sto l = some cl) (hcr : E0.sto r = some cr) (hW : WinInv cP i (promise cP i a0 v0 w))
    (h0P : ∃ th E, (promise cP i a0 v0 w).ths[i]? = some th ∧
      InvAtXRB p k arch i E0 n0 vw cP.mem thP.promises l cl (promise cP i a0 v0 w) th E ∧ E.pfr r = none) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PfrX p k arch cP i a0 v0 w r E0 n0 vw cP.mem thP.promises l cl := by
  intro c th hs hc hth
  obtain ⟨th', E, hth', hB, hpf⟩ := solo_typedXRP hP hsc hvI hwin hthP hpl hcl hcr hW h0P hs hc hPS hSub hSig
  rw [hth] at hth'
  cases hth'
  exact ⟨E, hB, hpf⟩

/-- **G-0 at any planted root edge**, `PfrX` discharged (`PfrX_of`), unused premises pruned. -/
theorem g0WinT_ofP {cP : Cfg} {thP : TTh} {a0 b a' : Address} {v0 : WeakMem.Val} {g : Nat} {w wt : Ts}
    {E0 : TEnv} {ca cr : Cell} {n0 vw : Nat} {l : AllocLabel} {cl : Cell} {t : Nat}
    [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i (promise cP i a0 v0 w) c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv (promise cP i a0 v0 w))
    (hwin : ∀ c0, Solo p k arch i (promise cP i a0 v0 w) c0 → Certified p k arch c0 i →
      NoHoldPubA p k arch E0 E0 i c0)
    (hthP : cP.ths[i]? = some thP) (hpl : ∀ t, t ∈ thP.promises → t < cP.mem.size)
    (hcl : E0.sto l = some cl) (hW : WinInv cP i (promise cP i a0 v0 w))
    (h0P : ∃ th E, (promise cP i a0 v0 w).ths[i]? = some th ∧
      InvAtXRB p k arch i E0 n0 vw cP.mem thP.promises l cl (promise cP i a0 v0 w) th E ∧ E.pfr r = none)
    (hmt : (promise cP i a0 v0 w).mem[t]? = some ⟨b, .loc a' g, wt⟩) (ha : a'.label = r)
    (hca : E0.sto b.label = some ca) (hno : Ty.noOwnIn [] ca.ty = true) (hrf : rgnFree ca.ty = true)
    (hcr : E0.sto r = some cr) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    G0WinW p k arch cP i a0 v0 w r wt := by
  have hPfr := PfrX_of (n0 := n0) (vw := vw) hP hsc hvI hwin hthP hpl hcl hcr hW h0P hPS hSub hSig
  intro c th hs hc hth
  obtain ⟨c', hrun, hn⟩ := hc
  have hNo := fun c th hs hc hth => noFulT (p := p) (k := k) (arch := arch) hthP hmt ha
    hca hno hrf hcr hPfr (c := c) (th := th) hs hc hth
  exact winLe_cert hNo (fun c hs => memT hthP hmt hs.toSolo) hrun hn hs th hth (hNo c th hs ⟨c', hrun, hn⟩ hth)

/-- **G-0** for `B` itself, `PfrX` discharged: `g0WinT_ofP` at `t = cP.mem.size`. -/
theorem g0Win_ofP {cP : Cfg} {thP : TTh} {a0 a' : Address} {g : Nat} {w : Ts} {E0 : TEnv} {ca cr : Cell}
    {n0 vw : Nat} {l : AllocLabel} {cl : Cell} [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i (promise cP i a0 (.loc a' g) w) c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv (promise cP i a0 (.loc a' g) w))
    (hwin : ∀ c0, Solo p k arch i (promise cP i a0 (.loc a' g) w) c0 → Certified p k arch c0 i →
      NoHoldPubA p k arch E0 E0 i c0)
    (hthP : cP.ths[i]? = some thP) (hpl : ∀ t, t ∈ thP.promises → t < cP.mem.size)
    (hcl : E0.sto l = some cl) (hW : WinInv cP i (promise cP i a0 (.loc a' g) w))
    (h0P : ∃ th E, (promise cP i a0 (.loc a' g) w).ths[i]? = some th ∧
      InvAtXRB p k arch i E0 n0 vw cP.mem thP.promises l cl (promise cP i a0 (.loc a' g) w) th E ∧
      E.pfr r = none)
    (ha : a'.label = r)
    (hca : E0.sto a0.label = some ca) (hno : Ty.noOwnIn [] ca.ty = true) (hrf : rgnFree ca.ty = true)
    (hcr : E0.sto r = some cr) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    G0Win p k arch cP i a0 (.loc a' g) w r :=
  g0WinT_ofP (g := g) (wt := w) (t := cP.mem.size) hP hsc hvI hwin hthP hpl hcl hW h0P
    (by simp only [promise, hthP, Array.getElem?_push_size]) ha hca hno hrf hcr hPS hSub hSig

end

end TermOwnG0

#print axioms TermOwnG0.soloNP_trans
#print axioms TermOwnG0.runNP_inv
#print axioms TermOwnG0.invAtXRB_ext
#print axioms TermOwnG0.invAtXRB_prom
#print axioms TermOwnG0.solo_typedXRP
#print axioms TermOwnG0.PfrX_of
#print axioms TermOwnG0.g0WinT_ofP
#print axioms TermOwnG0.g0Win_ofP
