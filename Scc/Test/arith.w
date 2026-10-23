-- Fixed-width and Int arithmetic.  Each check returns its own number on
-- failure; all passing returns 42.  Covers the division cases that fault on
-- x64 hardware (zero divisor, -2^63 / -1), wrapping, signed comparison and
-- shifts, sign-extending conversion, lanes, and Int `+`/`-`.
def main(u : Unit) : Int =
  let z = cvt U64 0
  let seven = cvt U64 7
  let q = fop div seven z
  let c1 = fcmp eq q z
  if c1 = 1 then
    let r = fop rem seven z
    let c2 = fcmp eq r seven
    if c2 = 1 then
      let mn = cvt I64 9223372036854775808
      let m1 = cvt I64 18446744073709551615
      let q2 = fop div mn m1
      let c3 = fcmp eq q2 mn
      if c3 = 1 then
        let r2 = fop rem mn m1
        let z64 = cvt I64 0
        let c4 = fcmp eq r2 z64
        if c4 = 1 then
          let five = cvt I64 5
          let q3 = fop div five z64
          let r3 = fop rem five z64
          let c5 = fcmp eq q3 z64
          let c6 = fcmp eq r3 five
          if c5 = 1 then
            if c6 = 1 then
              let a8 = cvt I8 127
              let o8 = cvt I8 1
              let s8 = fop add a8 o8
              let m8 = cvt I8 128
              let c7 = fcmp eq s8 m8
              if c7 = 1 then
                let z8 = cvt I8 0
                let c8 = fcmp lt s8 z8
                if c8 = 1 then
                  let u8 = cvt U8 255
                  let zu8 = cvt U8 0
                  let c9 = fcmp lt u8 zu8
                  if c9 = 0 then
                    let n7 = cvt I8 249
                    let two = cvt I8 2
                    let q8 = fop div n7 two
                    let n3 = cvt I8 253
                    let c10 = fcmp eq q8 n3
                    if c10 = 1 then
                      let n8 = cvt I8 248
                      let sh = fop shr n8 o8
                      let n4 = cvt I8 252
                      let c11 = fcmp eq sh n4
                      if c11 = 1 then
                        let w = cvt I32 u8
                        let s32 = cvt I32 4294967295
                        let c255 = cvt I32 255
                        let c12 = fcmp eq w c255
                        if c12 = 1 then
                          let i8b = cvt I8 255
                          let w2 = cvt I32 i8b
                          let c13 = fcmp eq w2 s32
                          if c13 = 1 then
                            let ou = cvt U8 1
                            let nine = cvt U8 9
                            let shl = fop shl ou nine
                            let twou = cvt U8 2
                            let c14 = fcmp eq shl twou
                            if c14 = 1 then
                              let ln = asLanes U8 578437695752307201
                              let l2 = lane ln 2
                              let three = cvt U8 3
                              let c15 = fcmp eq l2 three
                              if c15 = 1 then
                                let ff = cvt U8 255
                                let ln2 = setLane ln 2 ff
                                let l2b = lane ln2 2
                                let l3 = lane ln2 3
                                let four = cvt U8 4
                                let c16 = fcmp eq l2b ff
                                let c17 = fcmp eq l3 four
                                if c16 = 1 then
                                  if c17 = 1 then
                                    let d = 7 - 5
                                    if d = 2 then
                                      let s = 30 + 12
                                      let hi = bits mulhi 9223372036854775808 4
                                      if hi = 2 then
                                        let ct = bit1 ctz 0
                                        if ct = 64 then
                                          let pc = bit1 popcnt 255
                                          if pc = 8 then
                                            let ng = fop1 neg o8
                                            let c18 = fcmp eq ng i8b
                                            if c18 = 1 then
                                              ret s
                                            else
                                              ret 22
                                          else
                                            ret 21
                                        else
                                          ret 20
                                      else
                                        ret 19
                                    else
                                      ret 18
                                  else
                                    ret 17
                                else
                                  ret 16
                              else
                                ret 15
                            else
                              ret 14
                          else
                            ret 13
                        else
                          ret 12
                      else
                        ret 11
                    else
                      ret 10
                  else
                    ret 9
                else
                  ret 8
              else
                ret 7
            else
              ret 6
          else
            ret 5
        else
          ret 4
      else
        ret 3
    else
      ret 2
  else
    ret 1
