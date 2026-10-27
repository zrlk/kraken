import WeakCore.TermArchE

/-
# TermArchS — the spawn step simulates: TSO ⊆ ARM for every `StepsE` run, no premise

`TermArchE.tso_stepsE_subset_arm` takes the premise `SpawnSim` (a TSO spawn is matched by an ARM
spawn, keeping `CfgLeT`).  This module proves it (`spawn_sim`), so the headlines below hold for
all programs, spawning ones included.

`spawnKid` binds the argument words bumped to the parent's post-barrier `vRelSt`
(`TermSpawn.bumpW V w = {w with view := max w.view V, rts := max w.rts V}`), and that `V` is only
`≤` on ARM.  `Promises.TValLe` relates `rts` by `≤` (not `=`): every consumer of a register's
`rts` (`depRts` in a load's `depBound`, `storeOb` under `storeDepRts`, `ctrlRts`) is monotone, and
a smaller bound only allows more.  So the bumped words relate (`tvle_bump`), the parent relates by
`fenceS_sim`, and the child's box label is the same (`tidLabel`: `lbase`, `n`, `nalloc` agree).

* `spawn_sim : SpawnSim p k cap`.
* Headlines: `tso_stepsE_subset_arm'`, `tso_traces_subset_arm'`, `tso_stepsE_final_subset_arm'`
  (the `TermArchE` theorems with `SpawnSim` discharged).
-/

namespace TermArchS
open CoreLang CoreTerm TermRun TermArch TermSpawnStep TermExtStep TermArchE
open WeakMem (Val Address Ts Arch)

theorem tvle_bump {x y : Word} {Va Vt : Ts} (h : Promises.TValLe x y) (hV : Va ≤ Vt) :
    Promises.TValLe (TermSpawn.bumpW Va x) (TermSpawn.bumpW Vt y) :=
  ⟨h.val,
    Nat.max_le.2 ⟨Nat.le_trans h.rts (Nat.le_max_left _ _),
      Nat.le_trans hV (Nat.le_max_right _ _)⟩,
    Nat.max_le.2 ⟨Nat.le_trans h.view (Nat.le_max_left _ _),
      Nat.le_trans hV (Nat.le_max_right _ _)⟩⟩

theorem wsle_bump {Va Vt : Ts} (hV : Va ≤ Vt) :
    ∀ {wa wt : List Word}, WsLe wa wt →
      WsLe (wa.map (TermSpawn.bumpW Va)) (wt.map (TermSpawn.bumpW Vt))
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨tvle_bump h hV, wsle_bump hV hs⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem thsLe_push {A B : Array TTh} (h : ThsLe A B) {ta tt : TTh} (ht : TThLe ta tt)
    (htl : ta.tidLbl = tt.tidLbl) : ThsLe (A.push ta) (B.push tt) := by
  refine ⟨by simp [h.1], ?_⟩
  intro l xa xt hxa hxt
  rw [Array.getElem?_push] at hxa hxt
  by_cases hl : l = B.size
  · have hla : l = A.size := h.1 ▸ hl
    simp only [hl, ↓reduceIte, Option.some.injEq] at hxt
    simp only [hla, ↓reduceIte, Option.some.injEq] at hxa
    subst hxa hxt; exact ⟨ht, htl⟩
  · have hla : ¬ l = A.size := h.1 ▸ hl
    simp only [hl, hla, ↓reduceIte] at hxa hxt
    exact h.2 l xa xt hxa hxt

theorem allP_spawnT {c : Cfg} {i : Nat} {par kid : TTh} (hk : kid.promises = []) {t : Ts}
    (ht : t ∈ allP (spawnT c i par kid)) : t ∈ par.promises ∨ t ∈ allP c := by
  have e : t ∈ allP { c with ths := c.ths.set! i par } := by
    simp only [allP, spawnT, List.mem_flatMap, Array.toList_push, List.mem_append,
      List.mem_singleton] at ht ⊢
    obtain ⟨x, hx | rfl, htx⟩ := ht
    · exact ⟨x, hx, htx⟩
    · rw [hk] at htx; cases htx
  exact allP_set (c := c) rfl e

/-- **The spawn step simulates** (TSO → ARM), given `TValLe.rts : ≤`. -/
theorem spawn_sim (p : Prog) (k : Promises.Knobs) (cap : Nat) : SpawnSim p k cap := by
  intro ca ct ct' ⟨h, htr⟩ hsp
  cases hsp with
  | mk i x f a T ts e tt rt ws h1 h2 h3 h4 h5 =>
    obtain ⟨ta, ha, hta, htl⟩ := ths_some_tid h.ths h1
    obtain ⟨wa, hwa, hw⟩ := evalAt_tso hta.env h5
    have hn : ca.n = ct.n := by simp only [Cfg.n, h.ths.1, h.cap]
    have hlbl : tidLabel ca i ta = tidLabel ct i tt := by
      simp only [tidLabel, h.lbase, hn, hta.nalloc]
    have hs : StLe (allP ct) (stOf ca.mem ca.pairs ta) (stOf ct.mem ct.pairs tt) :=
      ⟨h.mem, h.pairs, hta.vs, hta.promises, hta.nalloc, hta.undefs,
       fun t ht => h.agree t (mem_allP h1 ht), h.agree⟩
    have hS : StLe (allP ct) (spawnS ca ta) (spawnS ct tt) := fenceS_sim hs .sy
    have hv := hS.vs
    refine ⟨spawnCfg ca i ta x e f ts T wa,
      Spawn.mk i x f a T ts e ta rt wa ha (hta.term.trans h2) (hta.promises.trans h3)
        (h.ths.1 ▸ h4) hwa, ⟨?_, htr⟩⟩
    have hpar : TThLe (spawnPar ca i ta x e) (spawnPar ct i tt x e) :=
      ⟨rfl, ⟨rfl, rfl, by simp only [hlbl]; exact WsLe.refl _, hta.env⟩, hta.σs, hta.stack, hv,
        hS.promises, by simp only [spawnPar, withS]; rw [hta.nalloc, htl], hS.undefs, hta.permit⟩
    have hparl : (spawnPar ca i ta x e).tidLbl = (spawnPar ct i tt x e).tidLbl := by
      simp only [spawnPar, htl, h.lbase, hn, hta.nalloc]
    have hkid : TThLe (spawnKid ca i ta f ts T wa) (spawnKid ct i tt f ts T ws) :=
      ⟨rfl, ⟨rfl, rfl, wsle_bump hv.vRelSt hw, trivial⟩, rfl, trivial,
        ⟨hv.coh, hv.vRd, hv.vWr, hv.vCtrl, hv.vPreBase, hv.vRelSt, rfl, hv.fwd⟩, rfl, rfl, rfl, .none⟩
    have hkidl : (spawnKid ca i ta f ts T wa).tidLbl = (spawnKid ct i tt f ts T ws).tidLbl := by
      simp only [spawnKid, hlbl]
    refine ⟨h.mem, h.pairs, thsLe_push (thsLe_set h.ths i hpar hparl) hkid hkidl, h.lbase,
      h.boxFence, fun t ht => ?_, h.cap, h.trace⟩
    rcases allP_spawnT (c := ct) rfl ht with ht | ht
    · have : t ∈ tt.promises := by simpa [spawnPar, withS, spawnS, fenceS, stOf] using ht
      exact h.agree t (mem_allP h1 this)
    · exact h.agree t ht

/-- **Headline (`StepsE`), no premise.**  Every TSO run of machine, extern and spawn steps is
matched by an ARM run with the same trace, terms, values and counters, and views and read
timestamps no higher. -/
theorem tso_stepsE_subset_arm' (p : Prog) (k : Promises.Knobs) (cap : Nat) {c0 c : Cfg}
    (hwf : ∀ t ∈ allP c0, t < c0.mem.size) (h : StepsE p k .tso cap c0 c) :
    ∃ c', StepsE p k .arm cap c0 c' ∧ CfgLe c' c ∧ c'.trace = c.trace :=
  tso_stepsE_subset_arm p k cap hwf (spawn_sim p k cap) h

/-- Every TSO trace is an ARM trace (`StepsE`, no premise). -/
theorem tso_traces_subset_arm' (p : Prog) (k : Promises.Knobs) (cap : Nat) {c0 : Cfg}
    (hwf : ∀ t ∈ allP c0, t < c0.mem.size) {tr : List Event}
    (h : STrE p k .tso cap c0 tr) : STrE p k .arm cap c0 tr :=
  tso_traces_subset_arm p k cap hwf (spawn_sim p k cap) h

/-- Final configurations (`StepsE`, no premise). -/
theorem tso_stepsE_final_subset_arm' (p : Prog) (k : Promises.Knobs) (cap : Nat) {c0 c : Cfg}
    (hwf : ∀ t ∈ allP c0, t < c0.mem.size) (h : StepsE p k .tso cap c0 c) (hf : c.final = true) :
    ∃ c', StepsE p k .arm cap c0 c' ∧ CfgLe c' c ∧ c'.trace = c.trace ∧ c'.final = true :=
  tso_stepsE_final_subset_arm p k cap hwf (spawn_sim p k cap) h hf

end TermArchS

#print axioms TermArchS.tvle_bump
#print axioms TermArchS.wsle_bump
#print axioms TermArchS.thsLe_push
#print axioms TermArchS.allP_spawnT
#print axioms TermArchS.spawn_sim
#print axioms TermArchS.tso_stepsE_subset_arm'
#print axioms TermArchS.tso_traces_subset_arm'
#print axioms TermArchS.tso_stepsE_final_subset_arm'
