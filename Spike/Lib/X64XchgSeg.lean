/-
**An exchange on x64 as one segment**, generic in the program and the
source construct: `lane_storeW`'s pattern (`Spike/Lib/X64LaneStore.lean`)
with any source at an exchange site (`XchgSite`) and the held word tracked.
The lowered code: a block `B1` (the base's load), the exchange's load
`movq i(%b), %t` (a hold, `holdLd_ndW`), a block `B2` and its store
`movq %t', i(%b)` (the exchange, `xchgSt_ndW`).

`B1` leaves the element's address in `%b + i` while the source takes a
local run to the exchange site; the load's value `r` and the held word `w'`
are related (`ms.rd w'`, `ValRep lbl w'.val r`, the memory side's facts at a
hold load), and the nodes past the load keep them, so the target node's
invariant `J'` may use them; `B2` keeps `%b + i` and puts the exchanged
value's word in `%t'`.

- `xsNL`, `xsNH`, `xsNS`: the load's node, `B2`'s node with the element
  held, the store's node;
- `xchg_segW`: the segment from the construct's node to the node after the
  store, the source past the exchange (`x` bound to the held word).
-/
import Spike.Lib.X64LaneStore

namespace Spike.Lib.X64.Flow

namespace XchgSeg

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib.X64
open Scc.Sem (ValRep)

section Nodes

variable {I : ISA} (ms : MemSide I) (lbl : WeakMem.AllocLabel → Option Nat) (lab : Label → Int64)
  (B1 B2 : List (Directive × Nat)) (pc pcL pcS : Int64) (zl : Nat) (o oL oS : SO) (t b : Reg64) (i : Int64)
  (J : AS → Ctl → Prop) (P : AS → Ctl → Ctl → Prop)

/-- The load's node: after `B1` from a state of `J` (its control `c0`),
the source at `c` reached from `c0` by a local run with `P σ0 c0 c` (the
exchange site). -/
def xsNL : ND := ⟨pcL, oL, fun σ c => ∃ σ0 c0, J σ0 c0 ∧ P σ0 c0 c ∧ σ = (arun lab B1 ⟨pc, o, σ0⟩).σ⟩

/-- `B2`'s node: after the load of `r`, the source holding the element's
address and the word `w'`, which the memory side relates to `r`. -/
def xsNH : ND := ⟨pcL + Int64.ofNat zl, oL.kill t, fun σ c => ∃ (σ0 : AS) (c0 c1 : Ctl) (r : BitVec 64)
  (w' : Word), J σ0 c0 ∧ P σ0 c0 c1 ∧ ms.rd w' ∧ ValRep lbl w'.val r.toNat ∧
  σ = ownStep t r (arun lab B1 ⟨pc, o, σ0⟩).σ ∧
  c = { c1 with hold := some ((bAddr (arun lab B1 ⟨pc, o, σ0⟩).σ.regs b i).toNat, w') }⟩

/-- The store's node: after `B2`, the source still holding. -/
def xsNS : ND := ⟨pcS, oS, fun σ c => ∃ (σ0 : AS) (c0 c1 : Ctl) (r : BitVec 64) (w' : Word),
  J σ0 c0 ∧ P σ0 c0 c1 ∧ ms.rd w' ∧ ValRep lbl w'.val r.toNat ∧
  σ = (arun lab B2 ⟨pcL + Int64.ofNat zl, oL.kill t, ownStep t r (arun lab B1 ⟨pc, o, σ0⟩).σ⟩).σ ∧
  c = { c1 with hold := some ((bAddr (arun lab B1 ⟨pc, o, σ0⟩).σ.regs b i).toNat, w') }⟩

end Nodes

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **An exchange**: from the node `⟨pc, o, J⟩` to the node after the
store with `J'`. At each state `σ`, control `c` of `J`: the source takes a
local run to a control `c1` at an exchange site of `x`'s word at `sa`
(`XchgSite`), no hold pending; after `B1`, `%b + i` represents `sa`; for
every loaded value `r` and held
word `w'` the memory side relates (`ms.rd w'`, `ValRep`), after the load and
`B2`: `%b + i` is unchanged, `%t'` represents the exchanged value's word,
and `J'` holds of the state there with the source past the exchange (`x`
bound to `w'`). The static runs of `B1` and `B2` reach the load's and the
store's pcs and offsets (`ha1`, `ha2`; the offsets their own refinement,
`hle`). The loaded register is not `%rsp` (`htr`). The states lie in `W`,
the nodes at the load and the store not moved by `Kw`, and at those nodes
`%b + i` is unmapped in private memory at the states in `W` (`hDL`,
`hDS`). -/
theorem xchg_segW {W : Frag isa} {Kw : State → State → Prop} {B1 B2 : List (Directive × Nat)}
    {pc pcL pcS : Int64} {zl zs : Nat} {o oL oS : SO} {lo hi : Int} {t b t' : Reg64} {i : Int64}
    {J J' : AS → Ctl → Prop}
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
    {P : AS → Ctl → Ctl → Prop}
    (hsrc : ∀ σ c, J σ c → ∃ c1, LocalRun p c c1 ∧ P σ c c1)
    (hsite : ∀ σ c c1, J σ c → P σ c c1 →
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c1 x sa u v e ∧ c1.hold = none ∧
      ValRep lbl (.loc sa 0) (bAddr (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ.regs b i).toNat ∧
      ∀ (r : BitVec 64) (w' : Word), ms.rd w' → ValRep lbl w'.val r.toNat →
        let σ1 := (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ
        let σ2 := (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat zl, oL.kill t, ownStep t r σ1⟩).σ
        bAddr σ2.regs b i = bAddr σ1.regs b i ∧
        (∃ tv wv, evalAt c1.env v = some (tv, [wv]) ∧ ValRep lbl wv.val ((σ2.regs.get64 t').setWidth 128).toNat) ∧
        J' σ2 ⟨e, (x, u, [w']) :: c1.env, none⟩)
    (hW1 : BlkW W Kw exe endPc R F ⟨pc, o, J⟩ B1)
    (hWL : ∀ s c, At exe endPc R F (xsNL (_root_.Executable.labels exe).label B1 pc pcL o oL J P) s c →
      W s c ∧ ∀ s', ¬ Kw s s')
    (hW2 : BlkW W Kw exe endPc R F (xsNH ms lbl (_root_.Executable.labels exe).label B1 pc pcL zl o oL t b i J P) B2)
    (hWS : ∀ s c, At exe endPc R F
      (xsNS ms lbl (_root_.Executable.labels exe).label B1 B2 pc pcL pcS zl o oL oS t b i J P) s c →
        W s c ∧ ∀ s', ¬ Kw s s')
    (hDL : ∀ s c σ, W s c → Abs R oL s.st.1 σ → F s.st.1 →
      (xsNL (_root_.Executable.labels exe).label B1 pc pcL o oL J P).J σ c →
      Mem.loadInt s.st.1.dmem (bAddr σ.regs b i) 8 = none)
    (hDS : ∀ s c σ, W s c → Abs R oS s.st.1 σ → F s.st.1 →
      (xsNS ms lbl (_root_.Executable.labels exe).label B1 B2 pc pcL pcS zl o oL oS t b i J P).J σ c →
      Mem.loadInt s.st.1.dmem (bAddr σ.regs b i) 8 = none) :
    SegW W Kw p lbl ms (At exe endPc R F ⟨pc, o, J⟩) (At exe endPc R F ⟨pcS + Int64.ofNat zs, oS, J'⟩) := by
  let lab := (_root_.Executable.labels exe).label
  let nL := xsNL lab B1 pc pcL o oL J P
  let nH := xsNH ms lbl lab B1 pc pcL zl o oL t b i J P
  let nS := xsNS ms lbl lab B1 B2 pc pcL pcS zl o oL oS t b i J P
  let nX : ND := ⟨pcS + Int64.ofNat zs, oS, J'⟩
  -- `B1`: the source's local run to the exchange site, the base loaded
  have s1 : SegW W Kw p lbl ms (At exe endPc R F ⟨pc, o, J⟩) (At exe endPc R F nL) := by
    refine (seg_ndW (N := fun _ : Unit => nL) (E := fun e : Empty => e.elim) h1ne hok1 hF hR hlo hhi hc1 hW1
      fun σ c hJ => ?_).mono_post fun s c h => ?_
    · obtain ⟨c1, hr, hP⟩ := hsrc σ c hJ
      exact ⟨c1, hr, .inl ⟨(), (ha1 σ).1.symm, by rw [(ha1 σ).2]; exact hle.1, σ, c, hJ, hP, rfl⟩⟩
    · rcases h with ⟨_, h⟩ | ⟨x, _⟩
      · exact h
      · exact x.elim
  -- the load, a hold
  have s2 : SegW W Kw p lbl ms (At exe endPc R F nL) (At exe endPc R F nH) := by
    refine (holdLd_ndWS (N := fun _ : Unit => nH) (E := fun e : Empty => e.elim) htr hF hc2 hWL hDL
      fun m σ c hA hD ⟨σ0, c0, hJ, hP, hσ⟩ => ?_).mono_post fun s c h => ?_
    · subst hσ
      obtain ⟨x, sa, u, v, e, hx, hh, hv, -⟩ := hsite σ0 c0 c hJ hP
      exact ⟨x, sa, u, v, e, hx, hv, hh, fun r w' hrd hrep =>
        .inl ⟨(), rfl, hle.2.1, σ0, c0, c, r.setWidth 64, w', hJ, hP, hrd, hrep, rfl, rfl⟩⟩
    · rcases h with ⟨_, h⟩ | ⟨x, _⟩
      · exact h
      · exact x.elim
  -- `B2`: the result stored, the word built, the element held
  have s3 : SegW W Kw p lbl ms (At exe endPc R F nH) (At exe endPc R F nS) := by
    refine (seg_ndW (N := fun _ : Unit => nS) (E := fun e : Empty => e.elim) h2ne hok2 hF hR hlo hhi hc3 hW2
      fun σ c ⟨σ0, c0, c1, r, w', hJ, hP, hrd, hrep, hσ, hc⟩ => ?_).mono_post fun s c h => ?_
    · subst hσ hc
      refine ⟨_, .refl _, .inl ⟨(), (ha2 _).1.symm, ?_, σ0, c0, c1, r, w', hJ, hP, hrd, hrep, rfl, rfl⟩⟩
      show SO.le oS (arun lab B2 ⟨pcL + Int64.ofNat zl, oL.kill t, _⟩).so = true
      rw [(ha2 _).2]; exact hle.2.2
    · rcases h with ⟨_, h⟩ | ⟨x, _⟩
      · exact h
      · exact x.elim
  -- the store, the exchange
  have s4 : SegW W Kw p lbl ms (At exe endPc R F nS) (At exe endPc R F nX) := by
    refine (xchgSt_ndWS (N := fun e : Empty => e.elim) (E := fun _ : Unit => nX) hc4 hWS hDS
      fun m σ c hA hD ⟨σ0, c0, c1, r, w', hJ, hP, hrd, hrep, hσ, hc⟩ => ?_).mono_post fun s c h => ?_
    · subst hσ hc
      obtain ⟨x, sa, u, v, e, hx, -, hv, hpost⟩ := hsite σ0 c0 c1 hJ hP
      obtain ⟨hr, ⟨tv, wv, hev, hval⟩, hJ'⟩ := hpost r w' hrd hrep
      refine ⟨x, sa, u, v, e, tv, wv, w', ?_, ?_, ?_, ?_, hval,
        .inr ⟨(), rfl, hle.2.2, hJ'⟩⟩
      · exact hx
      · rw [hr]; exact hv
      · rw [hr]
      · exact hev
    · rcases h with ⟨x, _⟩ | ⟨_, h⟩
      · exact x.elim
      · exact h
  exact (s1.seq s2).seq (s3.seq s4)

end XchgSeg

end Spike.Lib.X64.Flow
