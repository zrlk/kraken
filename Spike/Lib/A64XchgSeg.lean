/-
**An exchange on AArch64 as one segment**, generic in the program, the
source construct and the exchange's two instructions: `lane_storeW`'s
pattern (`Spike/Lib/A64LaneStore.lean`) with any source at an exchange site
(`XchgSite`), the held word tracked, and the load and the store any plain
8-byte access at an address function `ad` of the registers (`LdAt`,
`StAt`). x86-64's twin: `Spike/Lib/X64XchgSeg.lean`.

scc's `ldrOff`/`strOff` (`Scc/Emit/A64.lean`) emit a word access at
`[x10 + disp]` in one of three forms, by the displacement: the scaled
`ldr`/`str` (`exec_ldr`), the unscaled `ldur`/`stur` (`exec_ldur`), or
`movImm x16, disp` then the register-offset form `[x10, x16]`, whose
events Kraken's table does not list (`exec_ldrX`, `exec_strX` here, by
the same unfolding).

- `exec_ldrX`, `exec_strX`: the register-offset load and store;
- `LdAt`, `StAt`: a directive is a plain 8-byte load into `Xt` / store of
  `Xt` at the address `ad` of the registers; `ldAt_ldr`, `ldAt_ldur`,
  `ldAt_ldrX`, `stAt_str`, `stAt_stur`, `stAt_strX`;
- `holdLdG_ndW`, `xchgStG_ndW`: `holdLd_ndW`, `xchgSt_ndW` at any such
  directive; `holdLdG_ndWS`, `xchgStG_ndWS`: with the address unmapped in
  `dmem` from the states in `W`;
- `xsNL`, `xsNH`, `xsNS`: the load's node, `B2`'s node with the element
  held, the store's node;
- `xchg_segW`: the segment from the construct's node to the node after the
  store, the source past the exchange (`x` bound to the held word).
-/
import Spike.Lib.A64AllocNodes

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)

set_option linter.unusedSimpArgs false

/-! ## The register-offset forms -/

/-- `ofInt (x + y)` of a signed and an unsigned reading is the sum. -/
theorem ofInt_toInt_add_toNat (x y : BitVec 64) : BitVec.ofInt 64 (x.toInt + (y.toNat : Int)) = x + y := by
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt]
  congr 1
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

section Exec

variable {st : State} {sz : Nat}

/-- **`ldr Xt, [Xn, Xm]`** (`uxtx`, no shift), address unmapped in `dmem`:
one plain 8-byte load at `Xn + Xm`. -/
theorem exec_ldrX {dst : RegOrZr .W64} {n m : XReg}
    (hc : CellAt st (.instr ⟨.W64, .LDR dst (.addr ⟨.low (.reg n) .W64,
      .reg ⟨⟨.W64, .low (.reg m) .W64⟩, ⟨.UXTX, .E0⟩⟩⟩)⟩) sz)
    {a : BitVec 64} (ha : (st.st.1.regs.getXReg n).toBitVec + (st.st.1.regs.getXReg m).toBitVec = a)
    (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isaLSE2.exec st = some (.access st.decls a 8 fun l => .load .plain false l fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (v.setWidth 64) })) := by
  have ha' : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + ((st.st.1.regs.getXReg m).toNat : Int))
      = a := by rw [← ha, ← ofInt_toInt_add_toNat]; rfl
  show execLSE2 _ = _
  rw [execLSE2_of_cellAt_free hc trivial]
  simp [Directive.interp, Instr.interp, Operation.interp, AddrOrLit.interpLoad, AddrExpr.interpLoad,
    AddrExpr.checkSPAlignment, AddrExpr.eval, MachineData.load, RegOrSp.interpBase,
    toEv, EvTree.map, MachineData.setRegOrZr, MachineData.setRegOrSp, Reg64s.getRegOrSp,
    Reg64s.getRegOrSp64, RegOrSp.base, MemExtRegExpr.interp, BitVec.apply_mem_extend, ha', hdm]
  try (simp only [map_access, EvTree.map])
  try rfl

/-- **`str Xt, [Xn, Xm]`** (`uxtx`, no shift), address unmapped: one plain
8-byte store at `Xn + Xm`. -/
theorem exec_strX {src : RegOrZr .W64} {n m : XReg}
    (hc : CellAt st (.instr ⟨.W64, .STR src ⟨.low (.reg n) .W64,
      .reg ⟨⟨.W64, .low (.reg m) .W64⟩, ⟨.UXTX, .E0⟩⟩⟩⟩) sz)
    {a : BitVec 64} (ha : (st.st.1.regs.getXReg n).toBitVec + (st.st.1.regs.getXReg m).toBitVec = a)
    (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isaLSE2.exec st = some (.access st.decls a 8 fun l => .store .plain false l
      ((st.st.1.regs.getRegOrZr src).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  have ha' : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + ((st.st.1.regs.getXReg m).toNat : Int))
      = a := by rw [← ha, ← ofInt_toInt_add_toNat]; rfl
  show execLSE2 _ = _
  rw [execLSE2_of_cellAt_free hc trivial]
  simp [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpStore,
    AddrExpr.checkSPAlignment, AddrExpr.eval, MachineData.store, RegOrSp.interpBase,
    toEv, EvTree.map, MachineData.setRegOrZr, MachineData.setRegOrSp, Reg64s.getRegOrSp,
    Reg64s.getRegOrSp64, RegOrSp.base, MemExtRegExpr.interp, BitVec.apply_mem_extend, ha', hdm]
  try (simp only [map_access, EvTree.map])
  try rfl

end Exec

/-! ## Plain word accesses at an address function -/

/-- **`d` is a plain 8-byte load into `Xt` at `ad` of the registers**: at a
cell holding it, the address unmapped in `dmem` and agreeing with the
declarations, one load whose value lands in `Xt`. -/
def LdAt (d : Directive) (t : XReg) (ad : Reg64s → BitVec 64) : Prop :=
  ∀ (st : State) (a : BitVec 64), CellAt st d 4 → ad st.st.1.regs = a → Mem.loadInt st.st.1.dmem a 8 = none →
    st.decls.AgreesAt a 8 → isaLSE2.exec st = some (.load .plain false ⟨a, 8⟩ fun v =>
      .done (after st 4 { st.st.1 with regs := st.st.1.regs.setRegOrZr (.low (.reg t) .W64) (v.setWidth 64) }))

/-- **`d` is a plain 8-byte store of `Xt` at `ad` of the registers**: at a
cell holding it, the address unmapped in `dmem` and agreeing with the
declarations, one store of `Xt`, the machine data unchanged. -/
def StAt (d : Directive) (t : XReg) (ad : Reg64s → BitVec 64) : Prop :=
  ∀ (st : State) (a : BitVec 64), CellAt st d 4 → ad st.st.1.regs = a → Mem.loadInt st.st.1.dmem a 8 = none →
    st.decls.AgreesAt a 8 → isaLSE2.exec st = some (.store .plain false ⟨a, 8⟩
      ((st.st.1.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) fun _ => .done (after st 4 st.st.1))

theorem ldAt_ldr (t b : XReg) (i : Int64) : LdAt (ldrDir t b i) t (rAddr · b i) :=
  fun _ _ hc ha hdm hag => exec_ldr_agrees hc ha hdm hag

theorem stAt_str (t b : XReg) (i : Int64) : StAt (strDir t b i) t (rAddr · b i) :=
  fun _ _ hc ha hdm hag => exec_str_agrees hc ha hdm hag

/-- `ldur Xt, [Xn, #i]`, 64-bit. -/
def ldurDir (t b : XReg) (i : Int64) : Directive :=
  .instr ⟨.W64, .LDUR (.low (.reg t) .W64) ⟨.low (.reg b) .W64, .int64 i⟩⟩

/-- `stur Xt, [Xn, #i]`, 64-bit. -/
def sturDir (t b : XReg) (i : Int64) : Directive :=
  .instr ⟨.W64, .STUR (.low (.reg t) .W64) ⟨.low (.reg b) .W64, .int64 i⟩⟩

/-- `ldr Xt, [Xn, Xm]`, 64-bit. -/
def ldrXDir (t b m : XReg) : Directive :=
  .instr ⟨.W64, .LDR (.low (.reg t) .W64) (.addr ⟨.low (.reg b) .W64,
    .reg ⟨⟨.W64, .low (.reg m) .W64⟩, ⟨.UXTX, .E0⟩⟩⟩)⟩

/-- `str Xt, [Xn, Xm]`, 64-bit. -/
def strXDir (t b m : XReg) : Directive :=
  .instr ⟨.W64, .STR (.low (.reg t) .W64) ⟨.low (.reg b) .W64, .reg ⟨⟨.W64, .low (.reg m) .W64⟩, ⟨.UXTX, .E0⟩⟩⟩⟩

/-- The address `[Xn, Xm]` reads in the registers `r`. -/
def xAddr (r : Reg64s) (b m : XReg) : BitVec 64 := (r.getXReg b).toBitVec + (r.getXReg m).toBitVec

theorem ldAt_ldur (t b : XReg) (i : Int64) : LdAt (ldurDir t b i) t (rAddr · b i) := by
  intro st a hc ha hdm hag
  rw [exec_ldur hc ha hdm, access_agrees hag]

theorem stAt_stur (t b : XReg) (i : Int64) : StAt (sturDir t b i) t (rAddr · b i) := by
  intro st a hc ha hdm hag
  rw [exec_stur hc ha hdm, access_agrees hag]

theorem ldAt_ldrX (t b m : XReg) : LdAt (ldrXDir t b m) t (xAddr · b m) := by
  intro st a hc ha hdm hag
  rw [exec_ldrX hc ha hdm, access_agrees hag]

theorem stAt_strX (t b m : XReg) : StAt (strXDir t b m) t (xAddr · b m) := by
  intro st a hc ha hdm hag
  rw [exec_strX hc ha hdm, access_agrees hag]

/-! ## The nodes at any such load and store -/

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **`holdLd_ndWS` at any plain load** `d` into `Xt` at `ad` (`LdAt`), the
address unmapped in `dmem` at the states in `W` (`hdm`). -/
theorem holdLdG_ndWS {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {d : Directive} {t : XReg}
    {ad : Reg64s → BitVec 64} (hd : LdAt d t ad)
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hdm : ∀ s c σ, W s c → Abs R n.o s.st.1 σ → F s.st.1 → n.J σ c →
      Mem.loadInt s.st.1.dmem (ad σ.regs) 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (ad σ.regs).toNat ∧ c.hold = none ∧
        ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val (r.setWidth 64).toNat →
          Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t (r.setWidth 64) σ⟩
            { c with hold := some ((ad σ.regs).toNat, w') }) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hdm' := hdm s c σ (hW s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩).1 hA hD hJ
  have hc : CellAt s d 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨x, sa, u, v, e, hx, hv, hh, hL⟩ := hedge _ σ c hA hD hJ
  have ha : ad s.st.1.regs = ad σ.regs := by rw [hA.regs]
  have hex := hd s _ hc ha (by exact hdm') (agrees_of_decls hdc _ _)
  refine .holdLoad _ _ _ x sa u v e hex hx hv hh fun r w' hr hrep => ?_
  have hA' : Abs R (n.o.kill t)
      { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (r.setWidth 64) }
      (ldStep t (r.setWidth 64) σ) := by
    refine ⟨by simp only [ldStep, hA.regs], hA.status, ?_, hA.slot⟩
    exact hA.so.killZ (.low (.reg t) .W64) (r.setWidth 64)
  have hD' : F { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (r.setWidth 64) } :=
    hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s 4 { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (r.setWidth 64) } =
      { s with st := ({ s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (r.setWidth 64) },
        n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL r w' hr hrep with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨y, hy.at he hn hdc hA' hD'⟩

/-- **`holdLd_ndW` at any plain load** `d` into `Xt` at `ad` (`LdAt`). -/
theorem holdLdG_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {d : Directive} {t : XReg}
    {ad : Reg64s → BitVec 64} (hd : LdAt d t ad)
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      Mem.loadInt m.dmem (ad σ.regs) 8 = none ∧
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (ad σ.regs).toNat ∧ c.hold = none ∧
        ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val (r.setWidth 64).toNat →
          Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t (r.setWidth 64) σ⟩
            { c with hold := some ((ad σ.regs).toNat, w') }) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  holdLdG_ndWS hd hF hcode hW (fun _ _ σ _ hA hD hJ => (hedge _ σ _ hA hD hJ).1)
    fun m σ c hA hD hJ => (hedge m σ c hA hD hJ).2

/-- **`xchgSt_ndWS` at any plain store** `d` of `Xt` at `ad` (`StAt`), the
address unmapped in `dmem` at the states in `W` (`hdm`). -/
theorem xchgStG_ndWS {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {d : Directive} {t : XReg}
    {ad : Reg64s → BitVec 64} (hd : StAt d t ad)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hdm : ∀ s c σ, W s c → Abs R n.o s.st.1 σ → F s.st.1 → n.J σ c →
      Mem.loadInt s.st.1.dmem (ad σ.regs) 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
        (wv wold : TermRun.Word),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (ad σ.regs).toNat ∧
        c.hold = some ((ad σ.regs).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
        ValRep lbl wv.val ((σ.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ ⟨e, (x, u, [wold]) :: c.env, none⟩) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hdm' := hdm s c σ (hW s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩).1 hA hD hJ
  have hc : CellAt s d 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨x, sa, u, v, e, tv, wv, wold, hx, hrep, hh, hev, hV, hL⟩ := hedge _ σ c hA hD hJ
  have ha : ad s.st.1.regs = ad σ.regs := by rw [hA.regs]
  have hex := hd s _ hc ha (by exact hdm') (agrees_of_decls hdc _ _)
  rw [hA.regs] at hex
  refine .xchgStore _ _ _ _ x sa u v e tv wv wold hex hx hrep hh hev hV ?_
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-- **`xchgSt_ndW` at any plain store** `d` of `Xt` at `ad` (`StAt`). -/
theorem xchgStG_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {d : Directive} {t : XReg}
    {ad : Reg64s → BitVec 64} (hd : StAt d t ad)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      Mem.loadInt m.dmem (ad σ.regs) 8 = none ∧
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
        (wv wold : TermRun.Word),
        XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (ad σ.regs).toNat ∧
        c.hold = some ((ad σ.regs).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
        ValRep lbl wv.val ((σ.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128).toNat ∧
        Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ ⟨e, (x, u, [wold]) :: c.env, none⟩) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  xchgStG_ndWS hd hcode hW (fun _ _ σ _ hA hD hJ => (hedge _ σ _ hA hD hJ).1)
    fun m σ c hA hD hJ => (hedge m σ c hA hD hJ).2

end Fn

/-! ## The exchange's segment -/

namespace XchgSeg

section Nodes

variable (ms : MemSide isaLSE2) (lbl : WeakMem.AllocLabel → Option Nat) (lab : Label → Int64)
  (B1 B2 : List Directive) (pc pcL pcS : Int64) (o oL oS : SO) (t : XReg) (adL : Reg64s → BitVec 64)
  (J : AS → Ctl → Prop) (P : AS → Ctl → Ctl → Prop)

/-- The load's node: after `B1` from a state of `J` (its control `c0`),
the source at `c` reached from `c0` by a local run with `P σ0 c0 c` (the
exchange site). -/
def xsNL : ND := ⟨pcL, oL, fun σ c => ∃ σ0 c0, J σ0 c0 ∧ P σ0 c0 c ∧ σ = (arun lab B1 ⟨pc, o, σ0⟩).σ⟩

/-- `B2`'s node: after the load of `r`, the source holding the element's
address and the word `w'`, which the memory side relates to `r`. -/
def xsNH : ND := ⟨pcL + Int64.ofNat 4, oL.kill t, fun σ c => ∃ (σ0 : AS) (c0 c1 : Ctl) (r : BitVec 64)
  (w' : Word), J σ0 c0 ∧ P σ0 c0 c1 ∧ ms.rd w' ∧ ValRep lbl w'.val r.toNat ∧
  σ = ldStep t r (arun lab B1 ⟨pc, o, σ0⟩).σ ∧
  c = { c1 with hold := some ((adL (arun lab B1 ⟨pc, o, σ0⟩).σ.regs).toNat, w') }⟩

/-- The store's node: after `B2`, the source still holding. -/
def xsNS : ND := ⟨pcS, oS, fun σ c => ∃ (σ0 : AS) (c0 c1 : Ctl) (r : BitVec 64) (w' : Word),
  J σ0 c0 ∧ P σ0 c0 c1 ∧ ms.rd w' ∧ ValRep lbl w'.val r.toNat ∧
  σ = (arun lab B2 ⟨pcL + Int64.ofNat 4, oL.kill t, ldStep t r (arun lab B1 ⟨pc, o, σ0⟩).σ⟩).σ ∧
  c = { c1 with hold := some ((adL (arun lab B1 ⟨pc, o, σ0⟩).σ.regs).toNat, w') }⟩

end Nodes

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **An exchange**: from the node `⟨pc, o, J⟩` to the node after the
store with `J'`; the code a block `B1`, a plain load `dL` into `Xt` at
`adL` (`LdAt`), a block `B2`, a plain store `dS` of `Xt'` at `adS`
(`StAt`). At each state `σ`, control `c` of `J`: the source takes a local
run to a control `c1` at an exchange site of `x`'s word at `sa`
(`XchgSite`), no hold pending; after `B1`, `adL` represents `sa`; for every
loaded value `r` and held
word `w'` the memory side relates (`ms.rd w'`, `ValRep`), after the load and
`B2`: `adS` is the load's address, `Xt'` represents the exchanged value's
word, and `J'` holds of the state there with the source past the exchange
(`x` bound to `w'`). The static runs of `B1` and `B2` reach the load's and
the store's pcs and offsets (`ha1`, `ha2`; the offsets their own
refinement, `hle`). The states lie in `W`, the nodes at the load and the
store not moved by `Kw`, and at those nodes the access's address is
unmapped in private memory at the states in `W` (`hDL`, `hDS`). -/
theorem xchg_segW {W : Frag isaLSE2} {Kw : State → State → Prop} {B1 B2 : List Directive} {dL dS : Directive}
    {pc pcL pcS : Int64} {o oL oS : SO} {lo hi : Int} {t t' : XReg} {adL adS : Reg64s → BitVec 64}
    {J J' : AS → Ctl → Prop}
    (hdL : LdAt dL t adL) (hdS : StAt dS t' adS)
    (h1ne : B1 ≠ []) (h2ne : B2 ≠ []) (hok1 : okBlk lo hi o B1 = true) (hok2 : okBlk lo hi (oL.kill t) B2 = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc B1)
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcL [dL])
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pcL + Int64.ofNat 4) B2)
    (hc4 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcS [dS])
    (ha1 : ∀ σ, (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).pc = pcL ∧
      (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).so = oL)
    (ha2 : ∀ σ, (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat 4, oL.kill t, σ⟩).pc = pcS ∧
      (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat 4, oL.kill t, σ⟩).so = oS)
    (hle : SO.le oL oL = true ∧ SO.le (oL.kill t) (oL.kill t) = true ∧ SO.le oS oS = true)
    {P : AS → Ctl → Ctl → Prop}
    (hsrc : ∀ σ c, J σ c → ∃ c1, LocalRun p c c1 ∧ P σ c c1)
    (hsite : ∀ σ c c1, J σ c → P σ c c1 →
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c1 x sa u v e ∧ c1.hold = none ∧
      ValRep lbl (.loc sa 0) (adL (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ.regs).toNat ∧
      ∀ (r : BitVec 64) (w' : Word), ms.rd w' → ValRep lbl w'.val r.toNat →
        let σ1 := (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ
        let σ2 := (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat 4, oL.kill t, ldStep t r σ1⟩).σ
        adS σ2.regs = adL σ1.regs ∧
        (∃ tv wv, evalAt c1.env v = some (tv, [wv]) ∧
          ValRep lbl wv.val ((σ2.regs.getRegOrZr (.low (.reg t') .W64)).setWidth 128).toNat) ∧
        J' σ2 ⟨e, (x, u, [w']) :: c1.env, none⟩)
    (hW1 : BlkW W Kw exe endPc R F ⟨pc, o, J⟩ B1)
    (hWL : NodeW W Kw exe endPc R F (xsNL (_root_.Executable.labels exe).label B1 pc pcL o oL J P))
    (hW2 : BlkW W Kw exe endPc R F (xsNH ms lbl (_root_.Executable.labels exe).label B1 pc pcL o oL t adL J P) B2)
    (hWS : NodeW W Kw exe endPc R F
      (xsNS ms lbl (_root_.Executable.labels exe).label B1 B2 pc pcL pcS o oL oS t adL J P))
    (hDL : ∀ s c σ, W s c → Abs R oL s.st.1 σ → F s.st.1 →
      (xsNL (_root_.Executable.labels exe).label B1 pc pcL o oL J P).J σ c →
      Mem.loadInt s.st.1.dmem (adL σ.regs) 8 = none)
    (hDS : ∀ s c σ, W s c → Abs R oS s.st.1 σ → F s.st.1 →
      (xsNS ms lbl (_root_.Executable.labels exe).label B1 B2 pc pcL pcS o oL oS t adL J P).J σ c →
      Mem.loadInt s.st.1.dmem (adS σ.regs) 8 = none) :
    SegW W Kw p lbl ms (At exe endPc R F ⟨pc, o, J⟩) (At exe endPc R F ⟨pcS + Int64.ofNat 4, oS, J'⟩) := by
  let lab := (_root_.Executable.labels exe).label
  let nL := xsNL lab B1 pc pcL o oL J P
  let nH := xsNH ms lbl lab B1 pc pcL o oL t adL J P
  let nS := xsNS ms lbl lab B1 B2 pc pcL pcS o oL oS t adL J P
  let nX : ND := ⟨pcS + Int64.ofNat 4, oS, J'⟩
  -- `B1`: the source's local run to the exchange site, the address computed
  have s1 : SegW W Kw p lbl ms (At exe endPc R F ⟨pc, o, J⟩) (At exe endPc R F nL) := by
    refine (seg_ndW (N := fun _ : Unit => nL) (E := fun e : Empty => e.elim) h1ne hok1 hF hR hal hlo hhi hc1 hW1
      fun σ c hJ => ?_).mono_post fun s c h => ?_
    · obtain ⟨c1, hr, hP⟩ := hsrc σ c hJ
      exact ⟨c1, hr, .inl ⟨(), (ha1 σ).1.symm, by rw [(ha1 σ).2]; exact hle.1, σ, c, hJ, hP, rfl⟩⟩
    · rcases h with ⟨_, h⟩ | ⟨x, _⟩
      · exact h
      · exact x.elim
  -- the load, a hold
  have s2 : SegW W Kw p lbl ms (At exe endPc R F nL) (At exe endPc R F nH) := by
    refine (holdLdG_ndWS (N := fun _ : Unit => nH) (E := fun e : Empty => e.elim) hdL hF hc2 hWL hDL
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
    refine (seg_ndW (N := fun _ : Unit => nS) (E := fun e : Empty => e.elim) h2ne hok2 hF hR hal hlo hhi hc3 hW2
      fun σ c ⟨σ0, c0, c1, r, w', hJ, hP, hrd, hrep, hσ, hc⟩ => ?_).mono_post fun s c h => ?_
    · subst hσ hc
      refine ⟨_, .refl _, .inl ⟨(), (ha2 _).1.symm, ?_, σ0, c0, c1, r, w', hJ, hP, hrd, hrep, rfl, rfl⟩⟩
      show SO.le oS (arun lab B2 ⟨pcL + Int64.ofNat 4, oL.kill t, _⟩).so = true
      rw [(ha2 _).2]; exact hle.2.2
    · rcases h with ⟨_, h⟩ | ⟨x, _⟩
      · exact h
      · exact x.elim
  -- the store, the exchange
  have s4 : SegW W Kw p lbl ms (At exe endPc R F nS) (At exe endPc R F nX) := by
    refine (xchgStG_ndWS (N := fun e : Empty => e.elim) (E := fun _ : Unit => nX) hdS hc4 hWS hDS
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

end Spike.Lib.A64.Flow
