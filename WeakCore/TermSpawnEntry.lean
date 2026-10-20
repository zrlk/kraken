import WeakCore.TermSpawnKid
/-!
# TermSpawnEntry — a kid's entry frame at any cut

`TermInit.entryOK_of`, at a cut `Cut Eg i S` of any global environment about `p`, holding any total.
-/
namespace TermSpawn
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermSpawnSim

theorem finv_entry {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {th : TTh} {t r : Ty} {ws : List Word}
    {K : TEnv → List Word → Prop} (hK : ∀ E ws, K E ws)
    (henv : th.env = [("a", t, ws)]) (hσ : th.σs = [])
    (hv : VRR (fun _ => 0) (Cut Eg i S) t (shp t) ws .zero) (hlay : Lay [] t t ws) :
    FInv (fun _ => 0) (Cut Eg i S) th.σs K { vars := [("a", t, true)], ret := r } th.env := by
  have hRL : RLink (Cut Eg i S) := RLink_of (Coh_CE (Cut Eg i S)) (CohR_CE (Cut Eg i S))
  have hfind : ∀ x e, ([("a", t, true)] : List (String × Ty × Bool)).find? (·.1 == x) = some e →
      x = "a" ∧ e = ("a", t, true) := by
    intro x e h
    by_cases hx : "a" = x
    · subst hx; simp at h; exact ⟨rfl, h.symm⟩
    · have : ("a" == x) = false := by simpa using hx
      simp [List.find?, this] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k t' h; simp at h
  · intro x e hx
    obtain ⟨rfl, rfl⟩ := hfind x e hx
    refine ⟨t, ws, by rw [henv]; simp [lookupE], VRR_VR t hRL hv, by rw [hσ]; exact hlay⟩
  · intro _ _ _ _ _; exact hK _ _
  · refine ⟨fun k _ hk => by rw [hσ] at hk; exact absurd hk (Nat.not_lt_zero _), fun k σ h => by rw [hσ] at h; simp at h,
      fun k _ hk => by rw [hσ] at hk; exact absurd hk (Nat.not_lt_zero _)⟩
  · simp
  · refine ⟨fun k h => by simp [KEnv.ask] at h, fun k h => by simp [KEnv.ask] at h, fun σ h => by rw [hσ] at h; simp at h⟩
  · intro k; exact ⟨rfl, rfl, rfl⟩
  · intro k h; simp [KEnv.ask] at h
  · intro k h; simp [KEnv.ask] at h
  · intro k h; simp [KEnv.ask] at h
  · intro k h; simp [KEnv.ask] at h

/-- **A kid's entry frame** at `Cut Eg i S`, holding any total `Tot`, with an empty stack. -/
theorem entryR_of {p : Prog} {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {th : TTh} {f : String}
    {ts : List Ty} {t r : Ty} {ws : List Word} (Tot : Res) (hp : Eg.prog = p)
    (hterm : th.term = .tail f [] (.var "a") ts) (henv : th.env = [("a", t, ws)]) (hσ : th.σs = [])
    (hstk : th.stack = [])
    (hchk : check p { vars := [("a", t, true)], ret := r } (.tail f [] (.var "a") ts) = .ok ())
    (htv : TvOK { vars := [("a", t, true)], ret := r })
    (hv : VRR (fun _ => 0) (Cut Eg i S) t (shp t) ws .zero) (hlay : Lay [] t t ws)
    (hts : ts.all TermScope.argOK = true) (hwt : TermScope.wrapOK t = true) :
    ThInvRE p (Cut Eg i S) th Tot ∧ ThInvE p (Cut Eg i S) th := by
  have hfind : ∀ x e, ([("a", t, true)] : List (String × Ty × Bool)).find? (·.1 == x) = some e →
      x = "a" ∧ e = ("a", t, true) := by
    intro x e h
    by_cases hx : "a" = x
    · subst hx; simp at h; exact ⟨rfl, h.symm⟩
    · have : ("a" == x) = false := by simpa using hx
      simp [List.find?, this] at h
  have hE : EnvOK p (Cut Eg i S) := ⟨hp, Coh_CE (Cut Eg i S), CohR_CE (Cut Eg i S)⟩
  have hT : TypedK p (Cut Eg i S) { vars := [("a", t, true)], ret := r } th.term := by
    rw [hterm]
    exact ⟨check_sound p _ _ hchk, TermInit.checkW_tail_of hchk hts,
      fun v hm => by simp only [List.mem_singleton] at hm; subst hm; exact hwt,
      fun k hk _ => absurd hk (Nat.not_lt_zero _)⟩
  refine ⟨⟨fun _ => 0, Cut Eg i S, { vars := [("a", t, true)], ret := r }, Tot, .zero, rfl, hE, hT, htv,
    ⟨finv_entry (fun _ _ => trivial) henv hσ hv hlay, ?_, ?_⟩, Res.add_zero _,
    fun f rest h => by rw [hstk] at h; cases h⟩,
    ⟨fun _ => 0, Cut Eg i S, { vars := [("a", t, true)], ret := r }, rfl, hE, hT.1, htv, ?_⟩⟩
  · rw [hstk]; intro _ _ _ _ _ _; rfl
  · refine HeldOK_mono (Rf := .zero) ⟨by simp, by simp, fun y h => by simp at h, fun _ => .zero, fun x e hx _ => ?_, ?_⟩
      (Res.zero_le _)
    · obtain ⟨rfl, rfl⟩ := hfind x e hx
      exact ⟨t, ws, by rw [henv]; simp [lookupE], hv⟩
    · simp only [TermSound.Holds, List.filter, Bool.true_or, List.map, Res.sum_cons, Res.sum_nil, Res.add_zero]
      exact Res.le_refl _
  · rw [hstk]; exact ⟨finv_entry (fun _ _ => trivial) henv hσ hv hlay, fun _ _ h => by cases h⟩

end TermSpawn
