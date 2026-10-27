import WeakCore.ExtArmZ
import WeakCore.TermPermit
import WeakCore.SpawnVZ
import WeakCore.TermStartW
/-! # TermPermitV — (D4, T4(A) B1 = (i)) permits stay below the memory size

`PermV c`: every permit `some v` of `c` has `v ≤ c.mem.size`.  Carried beside `ViewInv` (which bounds the release
view an `unpark` passes), it holds along every `StepsE` run (`permit_le_size`): a thread step keeps each permit and
only grows the memory, a promise grows it, a spawn keeps the parent's permit and gives the child none, an extern step
keeps the memory and only clears (`park`) or keeps the caller's permit, and its wake joins `relView th.vs` (bounded by
`VSB`) or 0.  It holds at `startW` (`permV_startW`), so on such runs the cap in `parkVs` never applies
(`permit_cap`).  Non-root lemmas (the parkVs docstring cites `TermPermit.permit_le_size`).
-/

namespace TermPermit
open CoreLang CoreTerm TermRun TermExtStep TermSpawnStep TermViewInv
open WeakMem (Memory Ts Arch)

/-- Every permit is at most the memory size. -/
def PermV (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → ∀ (v : Ts), th.permit = some v → v ≤ c.mem.size

theorem permV_startW (p : Prog) (cap : Nat) : PermV (TermStartW.startW p cap) := by
  intro i th h v hv
  obtain ⟨-, rfl⟩ := TermStartW.startW_get h
  simp [TermStartW.wrapTh] at hv

/-- The cap never applies. -/
theorem permit_cap {c : Cfg} (h : PermV c) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) {v : Ts}
    (hp : th.permit = some v) : min v c.mem.size = v :=
  Nat.min_eq_left (h i th hth v hp)

theorem permV_getD {c : Cfg} (h : PermV c) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) :
    th.permit.getD 0 ≤ c.mem.size := by
  cases hp : th.permit with
  | none => exact Nat.zero_le _
  | some v => exact h i th hth v hp

theorem permV_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (hv : ViewInv c) (h0 : PermV c) (h : c' ∈ threadSteps p k arch c i) : PermV c' := by
  unfold threadSteps at h
  cases hth : c.ths[i]? with
  | none => rw [hth] at h; cases h
  | some th =>
    rw [hth] at h
    simp only [List.mem_map] at h
    obtain ⟨⟨mem', pairs', th'⟩, hr, rfl⟩ := h
    have hle := (tstep_V evalOp_V hr hv.1 (hv.2 i th hth)).2.1
    have hpm := tstep_permit_mem hr
    intro j t hj w hw
    rcases getElem?_set!_cases hj with rfl | hj
    · exact Nat.le_trans (h0 i th hth w (by rw [← hw]; exact hpm.symm)) hle
    · exact Nat.le_trans (h0 j t hj w hw) hle

theorem permV_prom {c : Cfg} {i : Nat} {a : WeakMem.Address} {v : WeakMem.Val} {w : Ts}
    (h0 : PermV c) : PermV (promise c i a v w) := by
  unfold promise
  cases hth : c.ths[i]? with
  | none => exact h0
  | some th =>
    have hle : c.mem.size ≤ (c.mem.push ⟨a, v, w⟩).size := by simp
    intro j t hj u hu
    rcases getElem?_set!_cases hj with rfl | hj
    · exact Nat.le_trans (h0 i th hth u hu) hle
    · exact Nat.le_trans (h0 j t hj u hu) hle

theorem permV_spawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    (h : Spawn p k arch cap c c') (h0 : PermV c) : PermV c' := by
  cases h with
  | mk i x f a T ts e th rt ws h1 _ _ _ _ =>
    intro j t hj u hu
    simp only [spawnCfg, spawnT] at hj
    rw [Array.getElem?_push] at hj
    split at hj
    · cases hj; simp [spawnKid] at hu
    · rcases getElem?_set!_cases hj with rfl | hj
      · exact h0 i th h1 u hu
      · exact h0 j t hj u hu

theorem permV_wake {c : Cfg} (h0 : PermV c) (i : Nat) {v : Ts} (hv : v ≤ c.mem.size) (n : ExtName)
    (ws : List Word) : PermV (wake c i v n ws) := by
  unfold wake
  split
  · split
    · rename_i j _
      unfold setPermit
      split
      · rename_i th0 hth0
        intro m t hm u hu
        rcases getElem?_set!_cases hm with rfl | hm
        · simp only [Option.some.injEq] at hu
          subst hu
          refine Nat.max_le.2 ⟨permV_getD h0 hth0, ?_⟩
          split
          · exact Nat.zero_le _
          · exact hv
        · exact h0 m t hm u hu
      · exact h0
    · exact h0
  · exact h0

theorem permV_extCfg {c : Cfg} (h0 : PermV c) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) (x : String)
    (n : ExtName) (e : Expr) (ws rs : List Word) : PermV (extCfg c i th x n e ws rs) := by
  intro j t hj u hu
  rw [extCfg_mem]
  unfold extCfg curCfg at hj
  split at hj
  · split at hj <;>
    · rcases getElem?_set!_cases hj with rfl | hj
      · exact h0 i th hth u hu
      · exact h0 j t hj u hu
  · rcases getElem?_set!_cases hj with rfl | hj
    · by_cases hn : n = .park
      · simp [hn] at hu
      · simp only [hn, ↓reduceIte] at hu
        exact h0 i th hth u hu
    · exact h0 j t hj u hu

theorem permV_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} (h : Ext p k arch c c')
    (hv : ViewInv c) (h0 : PermV c) : PermV c' := by
  obtain ⟨i, x, n, a, e, th, rt, ws, rs, hth, -, -, -, -, -, rfl⟩ := h.elim
  refine permV_wake (permV_extCfg h0 hth x n e ws rs) i ?_ n ws
  rw [extCfg_mem]
  obtain ⟨h1, h2, -, -, h5⟩ := (hv.2 i th hth).2.2
  exact Nat.max_le.2 ⟨h5, Nat.max_le.2 ⟨h1, h2⟩⟩

/-- **Permits stay below the memory size** along every `StepsE` run from a start with `ViewInv` and `PermV`. -/
theorem permit_le_size {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c0 c : Cfg} (hv : ViewInv c0)
    (h0 : PermV c0) (hr : StepsE p k arch cap c0 c) : PermV c :=
  (stepsG_pres (P := fun c => ViewInv c ∧ PermV c)
    (fun _ _ hs hp => ⟨viewInv_step hp.1 hs, by
      cases hs with
      | thread i hc _ => exact permV_thread hp.1 hp.2 hc
      | prom i a v w _ _ _ => exact permV_prom hp.2⟩)
    (fun _ _ hs hp => hs.elim
      (fun h => ⟨Z2SpawnV.viewInv_spawnStep h hp.1, permV_spawn h hp.2⟩)
      (fun h => ⟨ExtArmZ.viewInv_ext h hp.1, permV_ext h hp.1 hp.2⟩))
    hr ⟨hv, h0⟩).2

end TermPermit

#print axioms TermPermit.permV_startW
#print axioms TermPermit.permit_cap
#print axioms TermPermit.permit_le_size
