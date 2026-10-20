import WeakCore.TermOwnG0Defs
import WeakCore.TermTyped
import WeakCore.TermOwnG0W

/-!
# TermOwnG0: the G-0 window (`G0Win`) from the unplanted frontier along the typed run (`PfrX`)

Thread `i` plants `B` (index `cP.mem.size`, at `a0`, value `v0 = .loc a' g` with `a'.label = r`,
view `w`).  Route S:

* **(C) no fulfil before `publish r`** (`noFul`): at a certified configuration reached by `SoloNP r`,
  if `B` is no longer a promise, `MemOKP` types its message at `a0`'s cell (`noOwnIn`, `rgnFree`), so
  `wordOK_locPub` gives `r` a frontier or a box.  The tracked witness has neither (`PfrX`).
* **(R) the window** (`winLe_cert`): along the certificate of such a configuration, `B` stays
  outstanding until the first `publish r`, where `certified_pub_vWrLe` gives `vWr ≤ w`; `vWr` only grows.

`PfrX` (the tracked `InvAtXR` witness on the run has no frontier at `r` before `publish r`) is the named
hypothesis; it needs `PfrTag` from the step footprint.
-/

namespace TermOwnG0
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermOwnG0Defs TermOwnG0W
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The body of `InvAtXR` at a given thread state and environment (its `∃ th E` opened). -/
def InvAtXRB (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv) (n0 v0 : Nat)
    (mem0 : Memory) (P0 : List Ts) (l : AllocLabel) (cl : Cell) (c : Cfg) (th : TTh) (E : TEnv) : Prop :=
  Ext E0 E ∧ ThInvE p E th ∧ MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
    StoClo E ∧ (gOf p k arch c i).boxFence = true ∧ FrBound E0 n0 v0 E ∧ FrRunA E0 n0 v0 E (stOf c.mem c.pairs th) ∧
    RiniHeld E0 mem0 P0 l cl E th.vs.vWr

/-- **The unplanted frontier along the run** (named hypothesis, PFR-CHECK): at every certified
configuration reached by `SoloNP r` from the plant, the tracked `InvAtXR` witness environment (as a
`PfrTag`-strengthened `solo_typedXR` produces) has no frontier at `r`.  Intended under `ScopeAt`
along the run (as `g0Win_of`'s `hsc`): `intoRgn`/`validate` are out of scope (`PubScope` = `False`,
TermStep:31075), so the only `pfr`-setting thread step at `r` is a `publish` naming `r`. -/
def PfrX (p : Prog) (k : Promises.Knobs) (arch : Arch) (cP : Cfg) (i : Nat) (a0 : Address)
    (v0 : WeakMem.Val) (w : Ts) (r : AllocLabel) (E0 : TEnv) (n0 vw : Nat) (mem0 : Memory) (P0 : List Ts)
    (l : AllocLabel) (cl : Cell) : Prop :=
  ∀ c th, SoloNP p k arch i r (promise cP i a0 v0 w) c → Certified p k arch c i → c.ths[i]? = some th →
    ∃ E, InvAtXRB p k arch i E0 n0 vw mem0 P0 l cl c th E ∧ E.pfr r = none

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {r : AllocLabel}

theorem soloNP_snoc_thread {c0 c : Cfg} (h : SoloNP p k arch i r c0 c) :
    ∀ c1, c1 ∈ threadSteps p k arch c i → (∀ th, c.ths[i]? = some th → ¬ PubAt th r) →
      SoloNP p k arch i r c0 c1 := by
  induction h with
  | refl => exact fun c1 hs hn => .thread hs hn (.refl _)
  | thread hs' hn' _ ih => exact fun c1 hs hn => .thread hs' hn' (ih c1 hs hn)
  | prom a v w hw _ ih => exact fun c1 hs hn => .prom a v w hw (ih c1 hs hn)

theorem soloNP_snoc_prom {c0 c : Cfg} (h : SoloNP p k arch i r c0 c) :
    ∀ a v w, w < c.mem.size → SoloNP p k arch i r c0 (promise c i a v w) := by
  induction h with
  | refl => exact fun a v w hw => .prom a v w hw (.refl _)
  | thread hs' hn' _ ih => exact fun a v w hw => .thread hs' hn' (ih a v w hw)
  | prom a' v' w' hw' _ ih => exact fun a v w hw => .prom a' v' w' hw' (ih a v w hw)

/-- Any message of the plant configuration stays in memory along a run from it. -/
theorem memT {cP c : Cfg} {thP : TTh} {a0 : Address} {v0 : WeakMem.Val} {w : Ts} {t : Nat} {m : Msg}
    (hthP : cP.ths[i]? = some thP) (hmt : (promise cP i a0 v0 w).mem[t]? = some m)
    (h : Solo p k arch i (promise cP i a0 v0 w) c) : c.mem[t]? = some m := by
  have hext := solo_winInv h (winInv_refl (c0 := promise cP i a0 v0 w)
    (th0 := { thP with promises := thP.promises ++ [cP.mem.size] })
    (by simp only [promise, hthP]; exact arr_set hthP))
  obtain ⟨-, -, -, -, -, m2, -⟩ := hext
  exact m2 _ _ hmt

/-- `B`'s message stays in memory along a run from the plant. -/
theorem memB {cP c : Cfg} {thP : TTh} {a0 : Address} {v0 : WeakMem.Val} {w : Ts}
    (hthP : cP.ths[i]? = some thP) (h : Solo p k arch i (promise cP i a0 v0 w) c) :
    c.mem[cP.mem.size]? = some ⟨a0, v0, w⟩ :=
  memT hthP (by simp only [promise, hthP, Array.getElem?_push_size]) h

/-- **(C) for any planted root edge**: a message `⟨b, .loc a' g, wt⟩` at `t` in the plant
configuration (at a `noOwnIn`, `rgnFree` cell, `a'.label = r`) is still a promise of thread `i` at
every certified configuration reached by `SoloNP r`. -/
theorem noFulT {cP : Cfg} {thP : TTh} {a0 b a' : Address} {v0 : WeakMem.Val} {g : Nat} {w wt : Ts}
    {E0 : TEnv} {ca cr : Cell} {n0 vw : Nat} {l : AllocLabel} {cl : Cell} {t : Nat}
    (hthP : cP.ths[i]? = some thP) (hmt : (promise cP i a0 v0 w).mem[t]? = some ⟨b, .loc a' g, wt⟩)
    (ha : a'.label = r)
    (hca : E0.sto b.label = some ca) (hno : Ty.noOwnIn [] ca.ty = true) (hrf : rgnFree ca.ty = true)
    (hcr : E0.sto r = some cr) (hPfr : PfrX p k arch cP i a0 v0 w r E0 n0 vw cP.mem thP.promises l cl)
    {c : Cfg} {th : TTh} (hs : SoloNP p k arch i r (promise cP i a0 v0 w) c)
    (hc : Certified p k arch c i) (hth : c.ths[i]? = some th) : t ∈ th.promises := by
  apply Classical.byContradiction
  intro hB
  obtain ⟨E, ⟨hx, -, hm, -⟩, hpf⟩ := hPfr c th hs hc hth
  have hmB := memT hthP hmt hs.toSolo
  have hca' : E.sto b.label = some ca := hx.2.2.2.2.1 _ _ hca
  have hcr' : E.sto r = some cr := hx.2.2.2.2.1 _ _ hcr
  rcases hm.1.1 t ⟨b, .loc a' g, wt⟩ ca hB hmB hca' with h | h
  · cases h
  · rcases wordOK_locPub (a := a') (g := g) h hno hrf rfl with ⟨c1, f, -, hf⟩ | ⟨B, hbx⟩
    · rw [ha, hpf] at hf; cases hf
    · have h2 := (hm.2.2.2.2.2.2.2.2.2.1.2.2 _ _ hbx).1
      rw [ha, hcr'] at h2; cases h2

/-- **(C) No fulfil of `B` before `publish r`**: at a certified configuration reached by `SoloNP r`,
`B` is still a promise. -/
theorem noFul {cP : Cfg} {thP : TTh} {a0 a' : Address} {g : Nat} {w : Ts} {E0 : TEnv} {ca cr : Cell}
    {n0 vw : Nat} {l : AllocLabel} {cl : Cell}
    (hthP : cP.ths[i]? = some thP) (ha : a'.label = r)
    (hca : E0.sto a0.label = some ca) (hno : Ty.noOwnIn [] ca.ty = true) (hrf : rgnFree ca.ty = true)
    (hcr : E0.sto r = some cr) (hPfr : PfrX p k arch cP i a0 (.loc a' g) w r E0 n0 vw cP.mem thP.promises l cl)
    {c : Cfg} {th : TTh} (hs : SoloNP p k arch i r (promise cP i a0 (.loc a' g) w) c)
    (hc : Certified p k arch c i) (hth : c.ths[i]? = some th) : cP.mem.size ∈ th.promises :=
  noFulT (g := g) (wt := w) hthP (by simp only [promise, hthP, Array.getElem?_push_size]) ha hca hno hrf hcr hPfr hs hc hth

/-- **(R) The window along a certificate**: from a configuration reached by `SoloNP r` with a promise
`t` (message `m`) outstanding, a run to no promises meets a `publish r` with `t` outstanding first. -/
theorem winLe_cert {cP : Cfg} {a0 : Address} {v0 : WeakMem.Val} {w : Ts} {t : Nat} {m : Msg}
    (hNo : ∀ c th, SoloNP p k arch i r (promise cP i a0 v0 w) c → Certified p k arch c i →
      c.ths[i]? = some th → t ∈ th.promises)
    (hmB : ∀ c, SoloNP p k arch i r (promise cP i a0 v0 w) c → c.mem[t]? = some m)
    {c c' : Cfg} (h : Solo p k arch i c c') :
    noPromises c' i = true → SoloNP p k arch i r (promise cP i a0 v0 w) c → ∀ th, c.ths[i]? = some th →
      t ∈ th.promises → th.vs.vWr ≤ m.view := by
  induction h with
  | refl c =>
    intro hn _ th hth hB
    simp only [noPromises, hth, Option.map_some, Option.getD_some, List.isEmpty_iff] at hn
    rw [hn] at hB; cases hB
  | thread hs hrest ih =>
    rename_i c c1 c2
    intro hn hP th hth hB
    have hc1 : Certified p k arch c1 i := ⟨_, hrest, hn⟩
    by_cases hpub : PubAt th r
    · obtain ⟨y, a, e, -, -, -, hterm, -⟩ := hpub
      exact certified_pub_vWrLe hs hc1 hth hterm hB (hmB c hP)
    · have hP1 := soloNP_snoc_thread hP c1 hs (fun th' h' => by rw [hth] at h'; cases h'; exact hpub)
      obtain ⟨th0, th1, h0, h1, hv, -⟩ := winInv_thread (winInv_refl hth) hs
      rw [hth] at h0; cases h0
      exact Nat.le_trans hv (ih hn hP1 th1 h1 (hNo c1 th1 hP1 hc1 h1))
  | prom a v w' hw hrest ih =>
    rename_i c c2
    intro hn hP th hth hB
    have hP1 := soloNP_snoc_prom hP a v w' hw
    have h2 := ih hn hP1 _ (promise_inv (a := a) (v := v) (w := w') hth).2.1 (List.mem_append_left _ hB)
    exact h2

/-- **G-0 at any planted root edge** `t` (`B` itself or an older outstanding promise of thread
`i`) whose message `⟨b, .loc a' g, wt⟩` names `r`: the window `vWr ≤ wt`, from `PfrX`.  The
`solo_typedXR` premises are kept for the `PfrX` discharge. -/
theorem g0WinT_of {cP : Cfg} {thP : TTh} {a0 b a' : Address} {v0 : WeakMem.Val} {g : Nat} {w wt : Ts}
    {E0 : TEnv} {ca cr : Cell} {n0 vw : Nat} {l : AllocLabel} {cl : Cell} {t : Nat}
    [ProgRetIall p] (_hk : k.storeDepRts = true) (_hP : ProgT p)
    (_hsc : ∀ c0, Solo p k arch i (promise cP i a0 v0 w) c0 → Certified p k arch c0 i → ScopeAt p i c0)
    (_hwin : ∀ c0, Solo p k arch i (promise cP i a0 v0 w) c0 → Certified p k arch c0 i →
      NoHoldPub p k arch i c0)
    (hthP : cP.ths[i]? = some thP) (_hpl : ∀ t, t ∈ thP.promises → t < cP.mem.size)
    (_hcl : E0.sto l = some cl) (_hW : WinInv cP i (promise cP i a0 v0 w))
    (_h0 : InvAtXR p k arch i E0 n0 vw cP.mem thP.promises l cl (promise cP i a0 v0 w))
    (_ht : t = cP.mem.size ∨ t ∈ thP.promises)
    (hmt : (promise cP i a0 v0 w).mem[t]? = some ⟨b, .loc a' g, wt⟩) (ha : a'.label = r)
    (hca : E0.sto b.label = some ca) (hno : Ty.noOwnIn [] ca.ty = true) (hrf : rgnFree ca.ty = true)
    (hcr : E0.sto r = some cr) (hPfr : PfrX p k arch cP i a0 v0 w r E0 n0 vw cP.mem thP.promises l cl) :
    G0WinW p k arch cP i a0 v0 w r wt := by
  intro c th hs hc hth
  obtain ⟨c', hrun, hn⟩ := hc
  have hNo := fun c th hs hc hth => noFulT (p := p) (k := k) (arch := arch) hthP hmt ha
    hca hno hrf hcr hPfr (c := c) (th := th) hs hc hth
  exact winLe_cert hNo (fun c hs => memT hthP hmt hs.toSolo) hrun hn hs th hth (hNo c th hs ⟨c', hrun, hn⟩ hth)

/-- **G-0** (route S): the window `vWr ≤ w` at every certified configuration before `publish r`,
from the unplanted frontier `PfrX` on the tracked typed run: `g0WinT_of` at `t = cP.mem.size`. -/
theorem g0Win_of {cP : Cfg} {thP : TTh} {a0 a' : Address} {g : Nat} {w : Ts} {E0 : TEnv} {ca cr : Cell}
    {n0 vw : Nat} {l : AllocLabel} {cl : Cell} [ProgRetIall p] (_hk : k.storeDepRts = true) (_hP : ProgT p)
    (_hsc : ∀ c0, Solo p k arch i (promise cP i a0 (.loc a' g) w) c0 → Certified p k arch c0 i → ScopeAt p i c0)
    (_hwin : ∀ c0, Solo p k arch i (promise cP i a0 (.loc a' g) w) c0 → Certified p k arch c0 i →
      NoHoldPub p k arch i c0)
    (hthP : cP.ths[i]? = some thP) (_hpl : ∀ t, t ∈ thP.promises → t < cP.mem.size)
    (_hcl : E0.sto l = some cl) (_hW : WinInv cP i (promise cP i a0 (.loc a' g) w))
    (_h0 : InvAtXR p k arch i E0 n0 vw cP.mem thP.promises l cl (promise cP i a0 (.loc a' g) w))
    (ha : a'.label = r)
    (hca : E0.sto a0.label = some ca) (hno : Ty.noOwnIn [] ca.ty = true) (hrf : rgnFree ca.ty = true)
    (hcr : E0.sto r = some cr) (hPfr : PfrX p k arch cP i a0 (.loc a' g) w r E0 n0 vw cP.mem thP.promises l cl) :
    G0Win p k arch cP i a0 (.loc a' g) w r :=
  g0WinT_of (g := g) (wt := w) _hk _hP _hsc _hwin hthP _hpl _hcl _hW _h0 (Or.inl rfl) (by simp only [promise, hthP, Array.getElem?_push_size]) ha hca hno hrf hcr hPfr

end

end TermOwnG0

#print axioms TermOwnG0.soloNP_snoc_thread
#print axioms TermOwnG0.soloNP_snoc_prom
#print axioms TermOwnG0.memT
#print axioms TermOwnG0.memB
#print axioms TermOwnG0.noFulT
#print axioms TermOwnG0.noFul
#print axioms TermOwnG0.winLe_cert
#print axioms TermOwnG0.g0WinT_of
#print axioms TermOwnG0.g0Win_of
