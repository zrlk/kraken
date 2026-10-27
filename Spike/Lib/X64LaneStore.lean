/-
**A lane store on x64 as one segment**, generic in the program: the x64
twin of `Spike/Lib/A64LaneStore.lean`. The source construct
`let w = asLanes sg wd K in let o = xchg b[i] w in e`
(`Spike/Lib/LaneStoreSrc.lean`) against its lowered code, a block `B1`, the
exchange's load `movq i(%b), %t` (a hold, `holdLd_ndW`), a block `B2` and
its store `movq %t', i(%b)` (the exchange, `xchgSt_ndW`).

The code is given by its pieces at their pcs, with the cells' sizes (`zl`
the load's, `zs` the store's; x64 cells have no fixed size); the blocks'
effects are asked on their abstract runs (`arun`), which a caller computes
on concrete blocks (`block_spec`). `B1` takes the source's `asLanes` step
and leaves the element's address in `%b + i`; `B2` builds the word in `%t'`
and keeps `%b`; the source holds the element in between.

- `lsC1`: the control past `asLanes`, at the exchange;
- `lsNL`, `lsNH`, `lsNS`: the load's node, `B2`'s node with the element
  held, the store's node;
- `lane_storeW`: the segment from the construct's node to the node after
  the store, the source past the exchange (`o` bound to the held word).
-/
import Spike.Lib.X64AllocNodes
import Spike.Lib.LaneStoreSrc

namespace Spike.Lib.X64.Flow

namespace LaneStore

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib.X64
open Scc.Sem (ValRep)

/-- The construct's control past `asLanes`: at the exchange, `w` bound to
the lane word. -/
def lsC1 (w o bn : String) (sg : Bool) (wd : Wd) (K i : Nat) (e : Expr) (c : Spike.Lib.Ctl) : Spike.Lib.Ctl :=
  ⟨.let_ o (.xchgAt (.var bn) (.lit i) (.var w)) e, (w, .lanes sg wd, [cst (.num K)]) :: c.env, none⟩

section Nodes

variable (lab : Label → Int64) (B1 B2 : List (Directive × Nat)) (pc pcL pcS : Int64) (zl : Nat) (o oL oS : SO)
  (t b : Reg64) (i : Int64) (w ov bn : String) (sg : Bool) (wd : Wd) (K i' : Nat) (e : Expr) (J : AS → Ctl → Prop)

/-- The load's node: after `B1` from a state of `J`, the source at the
exchange. -/
def lsNL : ND := ⟨pcL, oL, fun σ c => ∃ σ0 c0, J σ0 c0 ∧ σ = (arun lab B1 ⟨pc, o, σ0⟩).σ ∧
  c = lsC1 w ov bn sg wd K i' e c0⟩

/-- `B2`'s node: after the load of `r`, the source holding the element's
address and a word `w'`. -/
def lsNH : ND := ⟨pcL + Int64.ofNat zl, oL.kill t, fun σ c => ∃ (σ0 : AS) (c0 : Spike.Lib.Ctl) (r : BitVec 64)
  (w' : Word), J σ0 c0 ∧ σ = ownStep t r (arun lab B1 ⟨pc, o, σ0⟩).σ ∧
  c = { lsC1 w ov bn sg wd K i' e c0 with hold := some ((bAddr (arun lab B1 ⟨pc, o, σ0⟩).σ.regs b i).toNat, w') }⟩

/-- The store's node: after `B2`, the source still holding. -/
def lsNS : ND := ⟨pcS, oS, fun σ c => ∃ (σ0 : AS) (c0 : Spike.Lib.Ctl) (r : BitVec 64) (w' : Word), J σ0 c0 ∧
  σ = (arun lab B2 ⟨pcL + Int64.ofNat zl, oL.kill t, ownStep t r (arun lab B1 ⟨pc, o, σ0⟩).σ⟩).σ ∧
  c = { lsC1 w ov bn sg wd K i' e c0 with hold := some ((bAddr (arun lab B1 ⟨pc, o, σ0⟩).σ.regs b i).toNat, w') }⟩

end Nodes

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The lane store**: from the node `⟨pc, o, J⟩` of the construct (fixed
syntax: `w`, `ov`, `bn`, `sg`, `wd`, the word `K < 2^64`, the index `i'`, the
rest `e`) to the node after the store with `J'` of the state there and the
control past the exchange, for every held word. At each state of `J`: `bn`
is a locative to a buffer of lanes at label `l` placed at `A`; after `B1`,
`%b` plus `i` is the element's address `A + 8·i'`, unmapped in private
memory under `F`; after the load and `B2`, `%b + i` is unchanged and `%t'`
holds `K`. The static runs of `B1` and `B2` reach the load's and the store's
pcs and offsets (`ha1`, `ha2`; the offsets their own refinement, `hle`).
The loaded register is not `%rsp` (`htr`). The states lie in `W`, none moved
by `K`. -/
theorem lane_storeW {W : Frag isa} {Kw : State → State → Prop} {B1 B2 : List (Directive × Nat)}
    {pc pcL pcS : Int64} {zl zs : Nat} {o oL oS : SO} {lo hi : Int} {t b t' : Reg64} {i : Int64}
    {w ov bn : String} {sg : Bool} {wd : Wd} {K i' : Nat} {e : Expr} {J J' : AS → Ctl → Prop}
    (h1ne : B1 ≠ []) (h2ne : B2 ≠ []) (hok1 : okBlk lo hi o B1 = true) (hok2 : okBlk lo hi (oL.kill t) B2 = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (htr : t ≠ .rsp)
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc B1)
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcL [(ldDir b i t, zl)])
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pcL + Int64.ofNat zl) B2)
    (hc4 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcS [(stDir b i t', zs)])
    (ha1 : ∀ σ, (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).pc = pcL ∧
      (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).so = oL)
    (ha2 : ∀ σ, (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat zl, oL.kill t, σ⟩).pc = pcS ∧
      (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat zl, oL.kill t, σ⟩).so = oS)
    (hle : SO.le oL oL = true ∧ SO.le (oL.kill t) (oL.kill t) = true ∧ SO.le oS oS = true)
    (hbw : bn ≠ w) (hK : K < 2 ^ 64)
    (ht : ∀ σ c, J σ c → c.term = .let_ w (.asLanes sg wd (.lit K)) (.let_ ov (.xchgAt (.var bn) (.lit i') (.var w)) e))
    (hsrc : ∀ σ c, J σ c → ∃ (ty : Ty) (pw : Word) (μ : Mode) (l : WeakMem.AllocLabel) (A : Nat),
      evalAt c.env (.var bn) = some (ty, [pw]) ∧ pw.val = .loc ⟨l, 0⟩ 0 ∧ bufElem ty = some (μ, .lanes sg wd) ∧
      lbl l = some A ∧
      (bAddr (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ.regs b i).toNat = A + 8 * i' ∧
      (∀ m, F m → Mem.loadInt m.dmem (bAddr (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ.regs b i) 8
        = none) ∧
      ∀ r : BitVec 64,
        let σ1 := (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ
        let σ2 := (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat zl, oL.kill t, ownStep t r σ1⟩).σ
        bAddr σ2.regs b i = bAddr σ1.regs b i ∧
        ((σ2.regs.get64 t').setWidth 128).toNat = K ∧
        ∀ wold : Word, J' σ2 ⟨e, (ov, .lanes sg wd, [wold]) :: (lsC1 w ov bn sg wd K i' e c).env, none⟩)
    (hW1 : BlkW W Kw exe endPc R F ⟨pc, o, J⟩ B1)
    (hWL : ∀ s c, At exe endPc R F
      (lsNL (_root_.Executable.labels exe).label B1 pc pcL o oL w ov bn sg wd K i' e J) s c → W s c ∧ ∀ s', ¬ Kw s s')
    (hW2 : BlkW W Kw exe endPc R F
      (lsNH (_root_.Executable.labels exe).label B1 pc pcL zl o oL t b i w ov bn sg wd K i' e J) B2)
    (hWS : ∀ s c, At exe endPc R F
      (lsNS (_root_.Executable.labels exe).label B1 B2 pc pcL pcS zl o oL oS t b i w ov bn sg wd K i' e J) s c →
        W s c ∧ ∀ s', ¬ Kw s s') :
    SegW W Kw p lbl ms (At exe endPc R F ⟨pc, o, J⟩) (At exe endPc R F ⟨pcS + Int64.ofNat zs, oS, J'⟩) := by
  let lab := (_root_.Executable.labels exe).label
  let nL := lsNL lab B1 pc pcL o oL w ov bn sg wd K i' e J
  let nH := lsNH lab B1 pc pcL zl o oL t b i w ov bn sg wd K i' e J
  let nS := lsNS lab B1 B2 pc pcL pcS zl o oL oS t b i w ov bn sg wd K i' e J
  let nX : ND := ⟨pcS + Int64.ofNat zs, oS, J'⟩
  -- `B1`: the `asLanes` step, to the load
  have s1 : SegW W Kw p lbl ms (At exe endPc R F ⟨pc, o, J⟩) (At exe endPc R F nL) := by
    refine (seg_ndW (N := fun _ : Unit => nL) (E := fun e : Empty => e.elim) h1ne hok1 hF hR hlo hhi hc1 hW1
      fun σ c hJ => ?_).mono_post fun s c h => ?_
    · obtain ⟨ty, pw, μ, l, A, hb, hpw, hbuf, hl, -⟩ := hsrc σ c hJ
      have hs := (LaneStoreSrc.laneStore (p := p) (ht σ c hJ) hbw hb hpw hbuf hl hK).1
      exact ⟨_, .single hs, .inl ⟨(), (ha1 σ).1.symm, by rw [(ha1 σ).2]; exact hle.1, σ, c, hJ, rfl, rfl⟩⟩
    · rcases h with ⟨_, h⟩ | ⟨x, _⟩
      · exact h
      · exact x.elim
  -- the load, a hold
  have s2 : SegW W Kw p lbl ms (At exe endPc R F nL) (At exe endPc R F nH) := by
    refine (holdLd_ndW (N := fun _ : Unit => nH) (E := fun e : Empty => e.elim) htr hF hc2 hWL
      fun m σ c hA hD ⟨σ0, c0, hJ, hσ, hc⟩ => ?_).mono_post fun s c h => ?_
    · subst hσ hc
      obtain ⟨ty, pw, μ, l, A, hb, hpw, hbuf, hl, hadr, hmem, -⟩ := hsrc σ0 c0 hJ
      obtain ⟨-, hx, hv, hh, -, -⟩ := LaneStoreSrc.laneStore (p := p) (ht σ0 c0 hJ) hbw hb hpw hbuf hl hK
      refine ⟨hmem m hD, ov, _, _, _, e, hx, by rw [hadr]; exact hv, hh, fun r w' _ _ =>
        .inl ⟨(), rfl, hle.2.1, σ0, c0, r.setWidth 64, w', hJ, rfl, rfl⟩⟩
    · rcases h with ⟨_, h⟩ | ⟨x, _⟩
      · exact h
      · exact x.elim
  -- `B2`: the word built, the element held
  have s3 : SegW W Kw p lbl ms (At exe endPc R F nH) (At exe endPc R F nS) := by
    refine (seg_ndW (N := fun _ : Unit => nS) (E := fun e : Empty => e.elim) h2ne hok2 hF hR hlo hhi hc3 hW2
      fun σ c ⟨σ0, c0, r, w', hJ, hσ, hc⟩ => ?_).mono_post fun s c h => ?_
    · subst hσ hc
      refine ⟨_, .refl _, .inl ⟨(), (ha2 _).1.symm, ?_, σ0, c0, r, w', hJ, rfl, rfl⟩⟩
      show SO.le oS (arun lab B2 ⟨pcL + Int64.ofNat zl, oL.kill t, _⟩).so = true
      rw [(ha2 _).2]; exact hle.2.2
    · rcases h with ⟨_, h⟩ | ⟨x, _⟩
      · exact h
      · exact x.elim
  -- the store, the exchange
  have s4 : SegW W Kw p lbl ms (At exe endPc R F nS) (At exe endPc R F nX) := by
    refine (xchgSt_ndW (N := fun e : Empty => e.elim) (E := fun _ : Unit => nX) hc4 hWS
      fun m σ c hA hD ⟨σ0, c0, r, w', hJ, hσ, hc⟩ => ?_).mono_post fun s c h => ?_
    · subst hσ hc
      obtain ⟨ty, pw, μ, l, A, hb, hpw, hbuf, hl, hadr, hmem, hpost⟩ := hsrc σ0 c0 hJ
      obtain ⟨-, hx, hv, -, hev, hk⟩ := LaneStoreSrc.laneStore (p := p) (ht σ0 c0 hJ) hbw hb hpw hbuf hl hK
      obtain ⟨hr, hval, hJ'⟩ := hpost r
      refine ⟨by rw [hr]; exact hmem m hD, ov, _, _, _, e, _, _, w', hx, ?_, ?_, hev, ?_,
        .inr ⟨(), rfl, hle.2.2, hJ' w'⟩⟩
      · rw [hr, hadr]; exact hv
      · rw [hr]
      · rw [hval]; exact hk
    · rcases h with ⟨x, _⟩ | ⟨_, h⟩
      · exact x.elim
      · exact h
  exact (s1.seq s2).seq (s3.seq s4)

end LaneStore

end Spike.Lib.X64.Flow
