import WeakCore.Syntax
import WeakCore.TermStartD
/-! # DmaRing: a two-slot DMA ring at a device start (the program is parsed from `ringSrc`)

A two-slot DMA ring: a hostile device (`serve`, `abort`, the reset-responsive `devMain`), a driver (`submit`,
`requestReset`, `main`), a handler stand-in (`isr`) and `setup`, started by the device-start wrapper. What the instance
theorems prove is **slot-ownership (token) race freedom**: the slot regions guard no buffer (each holds one unit cell);
the descriptor and data cells are public and unprotected; data-level DRF is deferred.
-/
namespace DmaRing
open CoreLang CoreTerm TermRun TermSound TermCut TermScope TermStartW TermStartD
open WeakMem (Arch)

def ringSrc : String := "

proto Slot = <0!, 1, 2!, 3 ; 0->1, 1->2, 2->3, 3->0 ; recover(1->0, 3->0)>
type SlotPkg = (exists a. Ptr pub Word[a, Slot]) * (Ptr pub U64 * Ptr pub U64)
type Ring2 = SlotPkg * SlotPkg
type DevArgs = (Ring2 * ((Ptr pub U64 * Reg[32, ro]) * ThreadId)) * U64

def mkSlot(u : Unit) : SlotPkg =
  -- The slot's region holds only this unit cell: it guards NO buffer. desc and dat below are public cells,
  -- outside the region and unprotected by the slot protocol (data-level race freedom is deferred).
  let p = new[Unit] u
  let <r, d, t0> = region p
  let wv = mkWord r Slot 0 t0
  let s = new[Word[r, Slot]] wv
  let s2 = publish s
  let sp = pack s2 at r : exists a. Ptr pub Word[a, Slot]
  let z = zero[U64]
  let c1 = new[U64] z
  let desc = publish c1
  let c2 = new[U64] z
  let dat = publish c2
  let bufs = (desc, dat)
  let pk = (sp, bufs)
  ret pk

device def serve(a : (SlotPkg * Reg[32, ro]) * ThreadId) : Unit =
  let (ps, h) = a
  let (pk, st) = ps
  let (w0, bufs) = pk
  let (desc, dat) = bufs
  let <r, w> = unpack w0
  cas acq w 2 -> 3 as t then
    let x = load desc
    let o = devOut[64] x
    let v = devChoice[64] ()
    let s = store dat v
    let sv = devChoice[32] ()
    let p = (st, sv)
    let e = devWrite[32] p
    let u = store rel w 0 with t
    let y = unpark h
    ret ()
  else
    ret ()

device def abort(pk : SlotPkg) : Unit =
  let (w0, bufs) = pk
  let <r, w> = unpack w0
  cas acq w 2 -> 3 as t then
    let u = store rel w 0 with t
    ret ()
  else
    ret ()

device def devMain(a : DevArgs) : Unit =
  let (da, n) = a
  let ni = toInt n
  if ni = 0 then
    ret ()
  else
    let pk = park ()
    let (sl, rest) = da
    let (s0, s1) = sl
    let (cs, h) = rest
    let (ctl, st) = cs
    let rq = load acq ctl
    let ri = toInt rq
    if ri = 1 then
      let u0 = abort(s0)
      let u1 = abort(s1)
      let z = zero[U64]
      let k = store rel ctl z
      let o1 = 1
      let one = cvt U64 o1
      let m = fop sub n one
      let a2 = (da, m)
      tail devMain(a2)
    else
      let b0 = (s0, st)
      let c0 = (b0, h)
      let u0 = serve(c0)
      let b1 = (s1, st)
      let c1 = (b1, h)
      let u1 = serve(c1)
      let o1 = 1
      let one = cvt U64 o1
      let m = fop sub n one
      let a2 = (da, m)
      tail devMain(a2)

def submit(a : (SlotPkg * U64) * ThreadId) : Int =
  let (pv, d) = a
  let (pk, v) = pv
  let (w0, bufs) = pk
  let (desc, dat) = bufs
  let <r, w> = unpack w0
  cas acq w 0 -> 1 as t then
    let s = store desc v
    let u = store rel w 2 with t
    let y = unpark d
    ret 1
  else
    ret 0

def isr(a : Reg[32, ro] * U64) : Unit =
  let (st, n) = a
  let ni = toInt n
  if ni = 0 then
    ret ()
  else
    let p = park ()
    let x = mmioRead[32, ro, acq] st
    let (st2, v) = x
    let o1 = 1
    let one = cvt U64 o1
    let m = fop sub n one
    let b = (st2, m)
    tail isr(b)

def requestReset(a : Ptr pub U64 * ThreadId) : Unit =
  let (ctl, d) = a
  let o = 1
  let one = cvt U64 o
  let k = store rel ctl one
  let y = unpark d
  ret ()

def main(a : (Ring2 * Ptr pub U64) * ThreadId) : Int =
  let (rc, d) = a
  let (sl, ctl) = rc
  let (s0, s1) = sl
  let i5 = 5
  let v5 = cvt U64 i5
  let q0 = (s0, v5)
  let p0 = (q0, d)
  let r0 = submit(p0)
  let q1 = (s1, v5)
  let p1 = (q1, d)
  let r1 = submit(p1)
  let rr = (ctl, d)
  let u = requestReset(rr)
  ret 0

def setup(st : Reg[32, ro]) : (Ring2 * Ptr pub U64) * DevArgs =
  let s0 = mkSlot(())
  let s1 = mkSlot(())
  let z = zero[U64]
  let o = new[U64] z
  let ctl = publish o
  let i2 = 2
  let n2 = cvt U64 i2
  let hb = (st, n2)
  let h = spawn isr hb : Reg[32, ro] * U64
  let sl = (s0, s1)
  let cs = (ctl, st)
  let rest = (cs, h)
  let da = (sl, rest)
  let i3 = 3
  let n3 = cvt U64 i3
  let dn = (da, n3)
  let ca = (sl, ctl)
  let r = (ca, dn)
  ret r
"

def ring : Prog := match Syntax.parseProg ringSrc with | .ok p => p | .error _ => []

/-- The device argument's type (`devMain`'s). -/
def ringDevTy : Ty :=
  match ring.find? (·.name == "devMain") with | some d => d.argTy | none => .unit

/-- The ring's device start: `devMain` spawned by the wrapper; thread 0's start argument is one read-only status
register handle at address 4096. -/
def ringBoard : Board := { dev := "devMain", devTy := ringDevTy, argTy := .opq (.reg .w32 .ro), args := [cst (.num 4096)] }

#eval match Syntax.parseProg ringSrc with | .ok p => s!"parsed {p.length} {p.map Decl.name}" | .error e => s!"PARSE {e.line}:{e.col} {e.msg}"
#eval match checkProg ring with | .ok _ => "checkProg ok" | .error e => e
#eval ProgScopeOKW ring
#eval ((ring.find? (·.name == ringBoard.dev)).map (·.kind == .device)).getD false
#eval match check ring (bcx ringBoard) (boardTerm ringBoard.dev ringBoard.devTy (mainRet ring)) with
  | .ok _ => "board check ok" | .error e => e
#eval match checkW ring (bcx ringBoard) (boardTerm ringBoard.dev ringBoard.devTy (mainRet ring)) with
  | .ok _ => "board checkW ok" | .error e => e
#eval allOK (boardTerm ringBoard.dev ringBoard.devTy (mainRet ring))
#eval drf ringBoard.argTy
#eval (TermClose.tb 0 ringBoard.argTy && TermTv.mg ringBoard.argTy && wrapOK ringBoard.argTy)
-- the Slot header parses to `slotP` (both recovery targets) and pwf accepts it
#eval pwf slotP
#eval (Syntax.parseProg "proto Slot = <0!, 1, 2!, 3 ; 0->1, 1->2, 2->3, 3->0 ; recover(1->0, 3->0)>\ndef f(a : exists r. Ptr pub Word[r, Slot]) : Unit = ret ()").toOption.map (fun p => p.map (·.argTy) == [.iex (.ptr .pub (.word (.var 0) slotP))])
-- one recovery target alone is also well formed; a target on a holding state is refused
#eval pwf { slotP with recover := [(3, 0)] }
#eval pwf { slotP with recover := [(2, 0)] }

/-- The start argument is well formed. -/
theorem ring_argOK : BoardArgOK ring ringBoard := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw; simp [ringBoard] at hw; exact ⟨4096, hw⟩
  · intro i; simp [ringBoard, VRR, VR, cst, Promises.TVal.mk0]
  · simp only [ringBoard, Lay]
    refine ⟨?_, rfl, ?_, ?_, rfl⟩
    · simp [ShapeC, cst, Promises.TVal.mk0]
      intro us h; simp [accs] at h; subst h; rfl
    · decide
    · simp [Valid, cst, Promises.TVal.mk0]

/-- **Slot-ownership (token) race freedom of the two-slot DMA ring**: along every run from its device start, no
region token is held by two threads' frames unless a promise owes it; so neither slot word's region is held by the
device thread and a CPU thread at once. In this program each slot region holds only a unit cell, so the theorem
guards no buffer: the descriptor and data cells are public and unprotected, and data-level DRF is deferred.
Trusted device assumption: the real device touches only what the code of the device's threads touches (the device
thread and every thread descended from it by spawns). -/
theorem dma_ring_tokens_unique_net {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} (B : BoardOK ring ringBoard)
    (hk : k.storeDepRts = true) {c : Cfg} (hr : TermExtStep.StepsE ring k arch 3 (startD ring ringBoard 3) c) :
    ∃ (Eg : TermCut.GEnv) (Tot HP : Nat → TermSound.Res) (HS : TermSound.Res) (cr db : Nat → WeakMem.Ts → TermSound.Res),
      TermMain.FrameTie ring k arch c Eg Tot ∧ TermMain.SysInvN ring k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      ∀ n, TermMain.Debt c db (.rg n) = 0 →
      ∀ i j, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  token_unique_net_board B hk hr

-- Register-range premises and their instance at the ring's start; the `.ro` arm's unused binder is `_`.
def regRanges (env : Env) : List (Nat × Nat) := env.filterMap fun
  | (_, .opq (.reg _ .ro), _) => none
  | (_, .opq (.reg w _), [a]) => some (wordNum a, Wd.bits w / 8)
  | (_, .opq (.blk n _ _ st _), [a]) => some (wordNum a, n * st)
  | _ => none
def RegsDisjoint (env : Env) : Prop := (regRanges env).Pairwise fun (a, l) (b, m) => a + l ≤ b ∨ b + m ≤ a
def RegsDisjointAll (c0 : Cfg) : Prop :=
  ((c0.ths.toList.map (·.env)).flatMap regRanges).Pairwise fun (a, l) (b, m) => a + l ≤ b ∨ b + m ≤ a
example : RegsDisjointAll (startD ring ringBoard 3) := by
  simp [RegsDisjointAll, startD, boardTh, ringBoard, regRanges]

end DmaRing
#print axioms TermStartD.initShape_startD
#print axioms TermStartD.runScope_startD
#print axioms TermStartD.token_unique_net_board
#print axioms TermStartD.token_unique_final_board
#print axioms TermStartD.machine_tokens_main_board
#print axioms TermStartD.reachable_typed_board
#print axioms DmaRing.dma_ring_tokens_unique_net
#print axioms DmaRing.ring_argOK
