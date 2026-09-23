// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build !purego

// This file contains constant-time, 64-bit assembly implementation of
// P256. The optimizations performed here are described in detail in:
// S.Gueron and V.Krasnov, "Fast prime field elliptic-curve cryptography with 
//                          256-bit primes"
// http://link.springer.com/article/10.1007%2Fs13389-014-0090-x
// https://eprint.iacr.org/2013/816.pdf

#include "textflag.h"

#define res_ptr R4
#define a_ptr   R5   
#define b_ptr   R6   

#define acc0    R7   
#define acc1    R8   
#define acc2    R9   
#define acc3    R10  
#define acc4    R11  
#define acc5    R12  
#define acc6    R13  
#define acc7    R14  

#define t0      R15  
#define t1      R16  
#define t2      R17  
#define t3      R18  
#define t4      R19
#define t5      R24
#define t6      R25

#define x0      R26
#define x1      R27
#define x2      R28
#define x3      R20

#define y0      R23
#define y1      a_ptr
#define y2      R21
#define y3      R31

#define hlp0    b_ptr
#define hlp1    t2

DATA p256const0<>+0x00(SB)/8, $0x00000000ffffffff
DATA p256const1<>+0x00(SB)/8, $0xffffffff00000001
DATA p256ordK0<>+0x00(SB)/8, $0xccd1c8aaee00bc4f
DATA p256ord<>+0x00(SB)/8, $0xf3b9cac2fc632551
DATA p256ord<>+0x08(SB)/8, $0xbce6faada7179e84
DATA p256ord<>+0x10(SB)/8, $0xffffffffffffffff
DATA p256ord<>+0x18(SB)/8, $0xffffffff00000000
DATA p256one<>+0x00(SB)/8, $0x0000000000000001
DATA p256one<>+0x08(SB)/8, $0xffffffff00000000
DATA p256one<>+0x10(SB)/8, $0xffffffffffffffff
DATA p256one<>+0x18(SB)/8, $0x00000000fffffffe
GLOBL p256const0<>(SB), 8, $8
GLOBL p256const1<>(SB), 8, $8
GLOBL p256ordK0<>(SB), 8, $8
GLOBL p256ord<>(SB), 8, $32
GLOBL p256one<>(SB), 8, $32

/* ---------------------------------------*/
// func p256MovCond(res, a, b *P256Point, cond int)
// If cond is 0, sets res = b, otherwise sets res = a.
TEXT ·p256MovCond(SB),NOSPLIT,$0
        MOVV    res+0(FP), res_ptr
        MOVV    a+8(FP), a_ptr
        MOVV    b+16(FP), b_ptr
        MOVV    cond+24(FP), t0

        // mask = -(cond != 0)
        SGTU    R0, t0, t1
        SUBV    t1, R0, t1

        // Select each limb as:
        //     b ^ ((a ^ b) & mask)
        //
        // The loop count is fixed at 12 and does not depend on cond.
        MOVV    $0, t2
        MOVV    $12, x0
        MOVV    $0, t3

p256MovCond_loop:
        MOVV    (t3)(a_ptr), t4
        MOVV    (t3)(b_ptr), t5
        XOR     t4, t5, t6
        AND     t1, t6, t6
        XOR     t5, t6, t6
        MOVV    t6, (t3)(res_ptr)

        ADDV    $8, t3, t3
        ADDV    $1, t2, t2
        BNE     t2, x0, p256MovCond_loop
        RET

/* ---------------------------------------*/
// func p256NegCond(val *p256Element, cond int)
// If cond is not 0, sets val = -val mod p (aka: val = P - val).
TEXT ·p256NegCond(SB),NOSPLIT,$0
        MOVV    val+0(FP), res_ptr
        MOVV    cond+8(FP), t0

        // mask = -(cond != 0)
        SGTU    R0, t0, acc4
        SUBV    acc4, R0, acc4

        // acc = poly
        MOVV    $-1, acc0
        MOVV    p256const0<>(SB), acc1
        MOVV    $0, acc2
        MOVV    p256const1<>(SB), acc3

        // Load the original value
        MOVV    (0*8)(res_ptr), t0
        MOVV    (1*8)(res_ptr), t1
        MOVV    (2*8)(res_ptr), t2
        MOVV    (3*8)(res_ptr), t3

        // Keep the original value for the final constant-time selection.
        MOVV    t0, x0
        MOVV    t1, x1
        MOVV    t2, x2
        MOVV    t3, x3

        // Speculatively subtract
        SUBV    t0, acc0, t0
        SUBV    t1, acc1, t5    // x1 - y1 = z1', if z1' > x1 then overflow     
        SGTU    t0, acc0, t4
        SUBV    t4, t5, t1      // z1' - c0 = z1, if z1 > z1' then overflow
        SGTU    t5, acc1, t6
        SGTU    t1, t5, t4
        OR      t4, t6
        SUBV    t2, acc2, t5
        SUBV    t6, t5, t2
        SGTU    t5, acc2, t4
        SGTU    t2, t5, t5
        OR      t4, t5
        SUBV    t3, acc3, t3
        SUBV    t5, t3

        // Select original value when cond == 0, negated value otherwise.
        // result = original ^ ((original ^ negated) & mask)
        XOR     x0, t0, t4
        AND     acc4, t4, t4
        XOR     x0, t4, t0

        XOR     x1, t1, t4
        AND     acc4, t4, t4
        XOR     x1, t4, t1

        XOR     x2, t2, t4
        AND     acc4, t4, t4
        XOR     x2, t4, t2

        XOR     x3, t3, t4
        AND     acc4, t4, t4
        XOR     x3, t4, t3

        MOVV    t0, (0*8)(res_ptr)
        MOVV    t1, (1*8)(res_ptr)
        MOVV    t2, (2*8)(res_ptr)
        MOVV    t3, (3*8)(res_ptr)
         RET

/* ---------------------------------------*/
// p256Select sets res to the point at index idx in the table.
// idx must be in [0, 16]. It executes in constant time.
// idx == 0 returns the point at infinity (all zeroes).
// idx in [1, 16] selects table[idx-1].
//
// func p256Select(res *P256Point, table *p256Table, idx int)
TEXT ·p256Select(SB),NOSPLIT,$0
        MOVV    idx+16(FP), t0
        MOVV    table+8(FP), a_ptr
        MOVV    res+0(FP), res_ptr

        // allones is used to invert the constant-time equality mask.
        MOVV    $-1, x2

        // Process all 12 limbs. For every limb, scan all 16 entries.
        // Both loop counts are fixed and independent of idx.
        MOVV    $0, x0
        MOVV    $12, x1

p256Select_limb:
        MOVV    $0, t1
        MOVV    a_ptr, t5
        MOVV    $0, t6

p256Select_entry:
        // i is 1..16. Build:
        //     mask = 0xffff...ffff iff idx == i
        XOR     t0, t1, t2
        SUBV    t2, R0, t3
        OR      t2, t3, t3
        SRAV    $63, t3, t3
        XOR     t3, x2, t3

        MOVV    (t5), t4
        AND     t3, t4, t4
        OR      t6, t4, t6

        ADDV    $96, t5, t5
        ADDV    $1, t1, t1
        BNE     t1, x1, p256Select_entry

        MOVV    t6, (res_ptr)
        ADDV    $8, a_ptr, a_ptr
        ADDV    $8, res_ptr, res_ptr
        ADDV    $1, x0, x0
        BNE     x0, x1, p256Select_limb

        RET

/* ---------------------------------------*/
// p256SelectAffine sets res to the point at index idx in the table.
// idx must be in [0, 32]. It executes in constant time.
// idx == 0 returns the point at infinity (all zeroes).
// idx in [1, 32] selects table[idx-1].
//
// func p256SelectAffine(res *p256AffinePoint, table *p256AffineTable, idx int)
TEXT ·p256SelectAffine(SB),NOSPLIT,$0
        MOVV    idx+16(FP), t0
        MOVV    table+8(FP), a_ptr
        MOVV    res+0(FP), res_ptr

        MOVV    $-1, x2

        // Process all 8 limbs (x and y), scanning all 32 entries.
        // The loop counts are fixed and independent of idx.
        MOVV    $0, x0
        MOVV    $8, x1
	MOVV	$32, x3

p256SelectAffine_limb:
        MOVV    $0, t1
        MOVV    a_ptr, t5
        MOVV    $0, t6

p256SelectAffine_entry:
        // i is 1..32. Build:
        //     mask = 0xffff...ffff iff idx == i
        XOR     t0, t1, t2
        SUBV    t2, R0, t3
        OR      t2, t3, t3
        SRAV    $63, t3, t3
        XOR     t3, x2, t3

        MOVV    (t5), t4
        AND     t3, t4, t4
        OR      t6, t4, t6

        ADDV    $64, t5, t5
        ADDV    $1, t1, t1
        BNE     t1, x3, p256SelectAffine_entry

        MOVV    t6, (res_ptr)
        ADDV    $8, a_ptr, a_ptr
        ADDV    $8, res_ptr, res_ptr
        ADDV    $1, x0, x0
        BNE     x0, x1, p256SelectAffine_limb

        RET

// func p256FromMont(res, in *p256Element)
TEXT ·p256FromMont(SB),NOSPLIT,$0-16
	MOVV	res+0(FP), res_ptr
	MOVV	in+8(FP), a_ptr

	MOVV	p256const0<>(SB), acc4      // const0 = acc4 (借用空闲的 acc4/acc5)
	MOVV	p256const1<>(SB), acc5      // const1 = acc5

	MOVV	0*8(a_ptr), acc0
	MOVV	1*8(a_ptr), acc1
	MOVV	2*8(a_ptr), acc2
	MOVV	3*8(a_ptr), acc3

	// ---------- Round 1: 消去 acc0 ----------
	SLLV	$32, acc0, t2               // sh = acc0<<32
	SRLV	$32, acc0, t0               // hi32 = acc0>>32
	MULV	acc0, acc5, t1              // lo = low(acc0*const1)
	MULHVU	acc0, acc5, acc0            // acc0 = high(acc0*const1)

	ADDV	t2, acc1, acc1              // acc1 += sh
	SGTU	t2, acc1, t3                // c1 = 溢出标志

	ADDV	t0, acc2, t4                // sum = acc2+hi32
	SGTU	t0, t4, t5
	ADDV	t4, t3, acc2                // acc2 = sum + c1
	SGTU	t4, acc2, t3
	ADDV	t5, t3, t3                  // c2

	ADDV	t1, acc3, t4
	SGTU	t1, t4, t5
	ADDV	t4, t3, acc3                // acc3 = sum + c2
	SGTU	t4, acc3, t3
	ADDV	t5, t3, t3                  // c3

	ADDV	t3, acc0, acc0              // acc0 += c3

	// ---------- Round 2: 消去 acc1 ----------
	SLLV	$32, acc1, t2
	SRLV	$32, acc1, t0
	MULV	acc1, acc5, t1
	MULHVU	acc1, acc5, acc1

	ADDV	t2, acc2, acc2
	SGTU	t2, acc2, t3

	ADDV	t0, acc3, t4
	SGTU	t0, t4, t5
	ADDV	t4, t3, acc3
	SGTU	t4, acc3, t3
	ADDV	t5, t3, t3

	ADDV	t1, acc0, t4
	SGTU	t1, t4, t5
	ADDV	t4, t3, acc0
	SGTU	t4, acc0, t3
	ADDV	t5, t3, t3

	ADDV	t3, acc1, acc1

	// ---------- Round 3: 消去 acc2 ----------
	SLLV	$32, acc2, t2
	SRLV	$32, acc2, t0
	MULV	acc2, acc5, t1
	MULHVU	acc2, acc5, acc2

	ADDV	t2, acc3, acc3
	SGTU	t2, acc3, t3

	ADDV	t0, acc0, t4
	SGTU	t0, t4, t5
	ADDV	t4, t3, acc0
	SGTU	t4, acc0, t3
	ADDV	t5, t3, t3

	ADDV	t1, acc1, t4
	SGTU	t1, t4, t5
	ADDV	t4, t3, acc1
	SGTU	t4, acc1, t3
	ADDV	t5, t3, t3

	ADDV	t3, acc2, acc2

	// ---------- Round 4: 消去 acc3 ----------
	SLLV	$32, acc3, t2
	SRLV	$32, acc3, t0
	MULV	acc3, acc5, t1
	MULHVU	acc3, acc5, acc3

	ADDV	t2, acc0, acc0
	SGTU	t2, acc0, t3

	ADDV	t0, acc1, t4
	SGTU	t0, t4, t5
	ADDV	t4, t3, acc1
	SGTU	t4, acc1, t3
	ADDV	t5, t3, t3

	ADDV	t1, acc2, t4
	SGTU	t1, t4, t5
	ADDV	t4, t3, acc2
	SGTU	t4, acc2, t3
	ADDV	t5, t3, t3

	ADDV	t3, acc3, acc3

	// ---------- 最终条件减模数：若 acc >= p，结果减 p ----------
	// p256P = {0xFFFFFFFFFFFFFFFF, const0, 0, const1}
	MOVV	$-1, t2                     // allones

	SUBV	t2, acc0, t0                // diff0 = acc0 - allones
	SGTU	t2, acc0, t1                // borrow0

	SUBV	acc4, acc1, x0              // tmp = acc1 - const0
	SGTU	acc4, acc1, x1
	SUBV	t1, x0, y1                  // diff1 = tmp - borrow0
	SGTU	t1, x0, x2
	ADDV	x1, x2, t1                  // borrow1

	SUBV	t1, acc2, x0                // diff2 = acc2 - 0 - borrow1
	SGTU	t1, acc2, t1                // borrow2

	SUBV	acc5, acc3, y2              // tmp = acc3 - const1
	SGTU	acc5, acc3, x3
	SUBV	t1, y2, y3                  // diff3 = tmp - borrow2
	SGTU	t1, y2, y0
	ADDV	x3, y0, t1                  // borrow3 (最终借位)

	// mask = 0 - borrow3： borrow3=0 -> mask=0(全零，选 diff)；borrow3=1 -> mask=全1(选 acc 原值)
	SUBV	t1, R0, t3                  // t3 = mask
	MOVV	$-1, t4
	XOR	t3, t4, t4                  // notmask = ^mask

	AND	t3, acc0, x1
	AND	t4, t0, x3
	OR	x1, x3, acc0

	AND	t3, acc1, x1
	AND	t4, y1, x3
	OR	x1, x3, acc1

	AND	t3, acc2, x1
	AND	t4, x0, x3
	OR	x1, x3, acc2

	AND	t3, acc3, x1
	AND	t4, y3, x3
	OR	x1, x3, acc3

	MOVV	acc0, 0*8(res_ptr)
	MOVV	acc1, 1*8(res_ptr)
	MOVV	acc2, 2*8(res_ptr)
	MOVV	acc3, 3*8(res_ptr)
	RET

/* ---------------------------------------*/  
// input:  x0-x3, y0-y3  
// output: x0-x3 = (y0-y3) - (x0-x3) mod p256P  
// uses:   const0(p256const0<>), const1(p256const1<>)  
// clobbers: y0-y3, acc0-acc7, t0-t3  
TEXT p256SubInternal<>(SB),NOSPLIT,$0  
	// ---- diff = y - x，借位链累积在 t0 ----  
	SUBV	x0, y0, acc0  
	SGTU	x0, y0, t0		// t0 = borrow0 = (y0 < x0)  
  
	SUBV	x1, y1, t1		// t1 = y1 - x1 (raw, 未计入 borrow0)  
	SGTU	x1, y1, t2		// t2 = raw borrow  
	SUBV	t0, t1, acc1		// acc1 = t1 - borrow0  
	SGTU	t0, t1, t3		// t3 = 减 borrow0 时是否又借位  
	OR	t2, t3, t0		// t0 = borrow1  
  
	SUBV	x2, y2, t1  
	SGTU	x2, y2, t2  
	SUBV	t0, t1, acc2  
	SGTU	t0, t1, t3  
	OR	t2, t3, t0		// t0 = borrow2  
  
	SUBV	x3, y3, t1  
	SGTU	x3, y3, t2  
	SUBV	t0, t1, acc3  
	SGTU	t0, t1, t3  
	OR	t2, t3, t0		// t0 = borrow3（最终借位：1 表示 y<x）  
  
	// ---- acc4..acc7 = diff + p256P（借位时需要加回的候选值）----  
	MOVV	$-1, t1				// p256P limb0  
	MOVV	p256const0<>(SB), t2		// p256P limb1  
	MOVV	p256const1<>(SB), t3		// p256P limb3  
  
	ADDV	t1, acc0, acc4  
	SGTU	t1, acc4, x0			// x0 = carry0  
  
	ADDV	t2, acc1, x1			// x1 = acc1 + const0 (raw)  
	SGTU	t2, x1, x2			// x2 = raw 进位  
	ADDV	x0, x1, acc5  
	SGTU	x0, acc5, x3			// x3 = 加 carry0 时是否又进位  
	OR	x2, x3, x0			// x0 = carry1  
  
	ADDV	x0, acc2, acc6			// limb2 的加数是 0，只需并入进位  
	SGTU	x0, acc6, x1  
	MOVV	x1, x0				// x0 = carry2  
  
	ADDV	t3, acc3, x2			// x2 = acc3 + const1 (raw)  
	ADDV	x0, x2, acc7			// acc7 = raw + carry2（最后一位无需再传递进位）  
  
	// ---- 常数时间选择：t0(最终借位)==0 选 diff，==1 选 diff+P ----  
	SUBV	t0, R0, t1			// t1 = mask：0（无借位）或全 1（借位）  
	MOVV	$-1, t2  
	XOR	t1, t2, t2			// t2 = notmask  
  
	AND	t2, acc0, t3  
	AND	t1, acc4, y0  
	OR	t3, y0, x0  
  
	AND	t2, acc1, t3  
	AND	t1, acc5, y0  
	OR	t3, y0, x1  
  
	AND	t2, acc2, t3  
	AND	t1, acc6, y0  
	OR	t3, y0, x2  
  
	AND	t2, acc3, t3  
	AND	t1, acc7, y0  
	OR	t3, y0, x3  
  
	RET

// p256SqrInternal computes acc0..acc3 = x0..x3 * x0..x3 mod P (Montgomery domain).  
// Clobbers t0-t6, acc0-acc7. Result left in acc0-acc3 (mirrors ARM64's y0-y3 output  
// convention is NOT followed here -- see note below).  
TEXT p256SqrInternal<>(SB),NOSPLIT,$0  
	// ---- x[1:] * x[0] ----  
	MULV	x0, x1, acc1  
	MULHVU	x0, x1, acc2  
  
	MULV	x0, x2, t0  
	ADDV	t0, acc2, acc2  
	SGTU	t0, acc2, t1  
	MULHVU	x0, x2, acc3  
	ADDV	t1, acc3, acc3  
  
	MULV	x0, x3, t0  
	ADDV	t0, acc3, acc3  
	SGTU	t0, acc3, t1  
	MULHVU	x0, x3, acc4  
	ADDV	t1, acc4, acc4  
  
	// ---- x[2:] * x[1] ----  
	MULV	x1, x2, t0  
	ADDV	t0, acc3, acc3  
	SGTU	t0, acc3, t2  
	MULHVU	x1, x2, t1  
	ADDV	t1, acc4, acc4  
	SGTU	t1, acc4, t3  
	ADDV	t2, acc4, acc4  
	SGTU	t2, acc4, t2  
	OR	t3, t2, t2  
	ADDV	t2, R0, acc5	// acc5 = carry-out (0 or 1)  
  
	MULV	x1, x3, t0  
	ADDV	t0, acc4, acc4  
	SGTU	t0, acc4, t1  
	MULHVU	x1, x3, t3  
	ADDV	t3, acc5, acc5  
	SGTU    t3, acc5, t4
	ADDV	t1, acc5, acc5  
	SGTU    t1, acc5, t5
	OR      t4, t5, hlp0
  
	// ---- x[3] * x[2] ----  
	MULV	x2, x3, t0  
	ADDV	t0, acc5, acc5  
	SGTU	t0, acc5, t1  
	MULHVU	x2, x3, acc6  
	ADDV	t1, acc6, acc6  
	ADDV    hlp0, acc6, acc6
  
	MOVV	$0, acc7  
  
	// ---- double all cross-products (acc1..acc6) ----  
	SLLV	$1, acc6, t0  
	SRLV	$63, acc5, t1  
	OR	t1, t0, t0  
	SLLV	$1, acc5, t1  
	SRLV	$63, acc4, t2  
	OR	t2, t1, t1  
	SLLV	$1, acc4, t2  
	SRLV	$63, acc3, t3  
	OR	t3, t2, t2  
	SLLV	$1, acc3, t3  
	SRLV	$63, acc2, t4  
	OR	t4, t3, t3  
	SLLV	$1, acc2, t4  
	SRLV	$63, acc1, t5  
	OR	t5, t4, t4  
	SLLV	$1, acc1, t5  
	SRLV	$63, acc6, acc7	// top carry-out of the double (from old acc6's high bit)  
	ADDV	acc7, R0, acc7  
	MOVV	t5, acc1  
	MOVV	t4, acc2  
	MOVV	t3, acc3  
	MOVV	t2, acc4  
	MOVV	t1, acc5  
	MOVV	t0, acc6  
  
	// ---- missing (diagonal) products: acc0 = x0*x0 low; add x0^2 high, x1^2, x2^2, x3^2 ----  
	MULV	x0, x0, acc0  
	MULHVU	x0, x0, t0  
	ADDV	t0, acc1, acc1  
	SGTU	t0, acc1, t1	// carry into acc2 (propagate below)  
  
	MULV	x1, x1, t0  
	ADDV	t0, acc2, acc2  
	SGTU	t0, acc2, t2  
	ADDV	t1, acc2, acc2  
	SGTU	t1, acc2, t3  
	OR	t2, t3, t1  
	MULHVU	x1, x1, t0  
	ADDV	t0, acc3, acc3  
	SGTU	t0, acc3, t2  
	ADDV	t1, acc3, acc3  
	SGTU	t1, acc3, t3  
	OR	t2, t3, t1  
  
	MULV	x2, x2, t0  
	ADDV	t0, acc4, acc4  
	SGTU	t0, acc4, t2  
	ADDV	t1, acc4, acc4  
	SGTU	t1, acc4, t3  
	OR	t2, t3, t1  
	MULHVU	x2, x2, t0  
	ADDV	t0, acc5, acc5  
	SGTU	t0, acc5, t2  
	ADDV	t1, acc5, acc5  
	SGTU	t1, acc5, t3  
	OR	t2, t3, t1  
  
	MULV	x3, x3, t0  
	ADDV	t0, acc6, acc6  
	SGTU	t0, acc6, t2  
	ADDV	t1, acc6, acc6  
	SGTU	t1, acc6, t3  
	OR	t2, t3, t1  
	MULHVU	x3, x3, t0  
	ADDV	t0, acc7, acc7  
	ADDV	t1, acc7, acc7  
  
	// ---- First reduction step ----  
	SLLV	$32, acc0, t2  
	SRLV	$32, acc0, t0  
	MOVV	p256const1<>(SB), t6
	MULV	acc0, t6, t1
	MULHVU	acc0, t6, acc0
	ADDV	t2, acc1, acc1  
	SGTU	t2, acc1, t3  
	ADDV	t0, acc2, acc2  
	SGTU	t0, acc2, t4  
	ADDV	t3, acc2, acc2  
	SGTU	t3, acc2, t5  
	OR	t4, t5, t3  
	ADDV	t1, acc3, acc3  
	SGTU	t1, acc3, t4  
	ADDV	t3, acc3, acc3  
	SGTU	t3, acc3, t5  
	OR	t4, t5, t3  
	ADDV	t3, acc0, acc0  
  
	// ---- Second reduction step ----  
	SLLV	$32, acc1, t2  
	SRLV	$32, acc1, t0  
	MOVV	p256const1<>(SB), t6
	MULV	acc1, t6, t1  
	MULHVU	acc1, t6, acc1  
	ADDV	t2, acc2, acc2  
	SGTU	t2, acc2, t3  
	ADDV	t0, acc3, acc3  
	SGTU	t0, acc3, t4  
	ADDV	t3, acc3, acc3  
	SGTU	t3, acc3, t5  
	OR	t4, t5, t3  
	ADDV	t1, acc0, acc0  
	SGTU	t1, acc0, t4  
	ADDV	t3, acc0, acc0  
	SGTU	t3, acc0, t5  
	OR	t4, t5, t3  
	ADDV	t3, acc1, acc1  
  
	// ---- Third reduction step ----  
	SLLV	$32, acc2, t2  
	SRLV	$32, acc2, t0  
	MOVV	p256const1<>(SB), t6
	MULV	acc2, t6, t1  
	MULHVU	acc2, t6, acc2  
	ADDV	t2, acc3, acc3  
	SGTU	t2, acc3, t3  
	ADDV	t0, acc0, acc0  
	SGTU	t0, acc0, t4  
	ADDV	t3, acc0, acc0  
	SGTU	t3, acc0, t5  
	OR	t4, t5, t3  
	ADDV	t1, acc1, acc1  
	SGTU	t1, acc1, t4  
	ADDV	t3, acc1, acc1  
	SGTU	t3, acc1, t5  
	OR	t4, t5, t3  
	ADDV	t3, acc2, acc2  
  
	// ---- Last reduction step ----  
	SLLV	$32, acc3, t2  
	SRLV	$32, acc3, t0  
	MOVV	p256const1<>(SB), t6
	MULV	acc3, t6, t1  
	MULHVU	acc3, t6, acc3  
	ADDV	t2, acc0, acc0  
	SGTU	t2, acc0, t3  
	ADDV	t0, acc1, acc1  
	SGTU	t0, acc1, t4  
	ADDV	t3, acc1, acc1  
	SGTU	t3, acc1, t5  
	OR	t4, t5, t3  
	ADDV	t1, acc2, acc2  
	SGTU	t1, acc2, t4  
	ADDV	t3, acc2, acc2  
	SGTU	t3, acc2, t5  
	OR	t4, t5, t3  
	ADDV	t3, acc3, acc3  
  
	// ---- Add bits [511:256] of the square result (acc4-acc7) ----  
	ADDV	acc4, acc0, acc0  
	SGTU	acc4, acc0, t0  
	ADDV	acc5, acc1, acc1  
	SGTU	acc5, acc1, t1  
	ADDV	t0, acc1, acc1  
	SGTU	t0, acc1, t2  
	OR	t1, t2, t0  
	ADDV	acc6, acc2, acc2  
	SGTU	acc6, acc2, t1  
	ADDV	t0, acc2, acc2  
	SGTU	t0, acc2, t2  
	OR	t1, t2, t0  
	ADDV	acc7, acc3, acc3  
	SGTU	acc7, acc3, t1  
	ADDV	t0, acc3, acc3  
	SGTU	t0, acc3, t2  
	OR	t1, t2, acc4	// final overflow bit (0 or 1)  
  
	// ---- Final conditional subtraction of P ----  
	SUBV	$-1, acc0, t0  
	SGTU	t0, acc0, t3  
	MOVV	p256const0<>(SB), t5
	SUBV	t5, acc1, t1  
	SGTU	t5, acc1, t4  
	SGTU	t3, t1, t5 
	SUBV	t3, t1, t1  
	OR	t4, t5, t3  
	SUBV	$0, acc2, t2  
	SGTU	t3, t2, t4  
	SUBV	t3, t2, t2
	MOVV	t4, t3  
	MOVV	p256const1<>(SB), t6
	SUBV	t6, acc3, y0  
	SGTU	y0, acc3, t4  
	SGTU	t3, y0, t5  
	SUBV	t3, y0, y0  
	OR	t4, t5, t3  
	SUBV	t3, acc4, acc4  
  
	// mask: acc4==0 (no final borrow, i.e. CS set) -> select t0..t2,y0 ; else acc0..acc3  
	SRAV    $63, acc4, t3
	MOVV	$-1, t4  
	XOR	t3, t4, t4  
  
	AND	t4, t0, t5  
	AND	t3, acc0, t6  
	OR	t5, t6, acc0 
  
	AND	t4, t1, t5  
	AND	t3, acc1, t6  
	OR	t5, t6, acc1
  
	AND	t4, t2, t5  
	AND	t3, acc2, t6  
	OR	t5, t6, acc2
  
	AND	t4, y0, t5  
	AND	t3, acc3, t6  
	OR	t5, t6, acc3

	MOVV	acc0, y0
	MOVV	acc1, y1
	MOVV	acc2, y2
	MOVV	acc3, y3
  
	RET

// func p256Sqr(res, in *p256Element, n int)
TEXT ·p256Sqr(SB),NOSPLIT,$0
	MOVV	res+0(FP), res_ptr
	MOVV	in+8(FP), a_ptr
	MOVV	n+16(FP), b_ptr

	MOVV	0*8(a_ptr), x0
	MOVV	1*8(a_ptr), x1
	MOVV	2*8(a_ptr), x2
	MOVV	3*8(a_ptr), x3

sqrLoop:
	SUBV	$1, b_ptr, b_ptr
	CALL	p256SqrInternal<>(SB)
	MOVV	y0, x0
	MOVV	y1, x1
	MOVV	y2, x2
	MOVV	y3, x3
	BNE	b_ptr, R0, sqrLoop

	MOVV	y0, 0*8(res_ptr)
	MOVV	y1, 1*8(res_ptr)
	MOVV	y2, 2*8(res_ptr)
	MOVV	y3, 3*8(res_ptr)
	RET


TEXT p256MulInternal<>(SB),NOSPLIT,$0
    // ==================== y0 * x ====================
    MULV    y0, x0, acc0
    MULHVU  y0, x0, acc1

    MULV    y0, x1, t0
    ADDV    t0, acc1, acc1
    SGTU    t0, acc1, t1
    MULHVU  y0, x1, acc2
    ADDV    t1, acc2, acc2

    MULV    y0, x2, t0
    ADDV    t0, acc2, acc2
    SGTU    t0, acc2, t1
    MULHVU  y0, x2, acc3
    ADDV    t1, acc3, acc3

    MULV    y0, x3, t0
    ADDV    t0, acc3, acc3
    SGTU    t0, acc3, t1
    MULHVU  y0, x3, acc4
    ADDV    t1, acc4, acc4

    // ---- 第一次约简 ----
    SLLV    $32, acc0, t2
    SRLV    $32, acc0, t0
    MOVV    p256const1<>(SB), t6
    MULV    acc0, t6, t1
    MULHVU  acc0, t6, acc0

    ADDV    t2, acc1, acc1
    SGTU    t2, acc1, t3
    ADDV    t0, acc2, acc2
    SGTU    t0, acc2, t4
    ADDV    t3, acc2, acc2
    SGTU    t3, acc2, t3
    OR      t4, t3, t3
    ADDV    t1, acc3, acc3
    SGTU    t1, acc3, t4
    ADDV    t3, acc3, acc3
    SGTU    t3, acc3, t3
    OR      t4, t3, t3
    ADDV    t3, acc0, acc0

    // ==================== y1 * x ====================
    MULV    y1, x0, t0
    ADDV    t0, acc1, acc1
    SGTU    t0, acc1, t1
    MULHVU  y1, x0, t2

    MULV    y1, x1, t0
    ADDV    t0, acc2, acc2
    SGTU    t0, acc2, t3
    MULHVU  y1, x1, t4

    MULV    y1, x2, t0
    ADDV    t0, acc3, acc3
    SGTU    t0, acc3, t5
    MULHVU  y1, x2, acc4
    ADDV    t5, acc4, acc4

    MULV    y1, x3, t0
    ADDV    t0, acc4, acc4
    SGTU    t0, acc4, t5
    MULHVU  y1, x3, acc5
    ADDV    t5, acc5, acc5

    ADDV    t2, acc2, acc2
    SGTU    t2, acc2, t2
    ADDV    t1, acc2, acc2
    SGTU    t1, acc2, t1
    OR      t2, t1, t1
    ADDV    t4, acc3, acc3
    SGTU    t4, acc3, t4
    ADDV    t3, acc3, acc3
    SGTU    t3, acc3, t3
    OR      t4, t3, t3
    ADDV    t1, acc3, acc3
    SGTU    t1, acc3, t1
    OR      t3, t1, t1
    ADDV    t1, acc5, acc5

    // ---- 第二次约简 ----
    SLLV    $32, acc1, t2
    SRLV    $32, acc1, t0
    MOVV    p256const1<>(SB), t6
    MULV    acc1, t6, t1
    MULHVU  acc1, t6, acc1

    ADDV    t2, acc2, acc2
    SGTU    t2, acc2, t3
    ADDV    t0, acc3, acc3
    SGTU    t0, acc3, t4
    ADDV    t3, acc3, acc3
    SGTU    t3, acc3, t3
    OR      t4, t3, t3
    ADDV    t1, acc0, acc0
    SGTU    t1, acc0, t4
    ADDV    t3, acc0, acc0
    SGTU    t3, acc0, t3
    OR      t4, t3, t3
    ADDV    t3, acc1, acc1

    // ==================== y2 * x ====================
    MULV    y2, x0, t0
    ADDV    t0, acc2, acc2
    SGTU    t0, acc2, t1
    MULHVU  y2, x0, t2

    MULV    y2, x1, t0
    ADDV    t0, acc3, acc3
    SGTU    t0, acc3, t3
    MULHVU  y2, x1, t4

    MULV    y2, x2, t0
    ADDV    t0, acc4, acc4
    SGTU    t0, acc4, t5
    MULHVU  y2, x2, acc5
    ADDV    t5, acc5, acc5

    MULV    y2, x3, t0
    ADDV    t0, acc5, acc5
    SGTU    t0, acc5, t5
    MULHVU  y2, x3, acc6
    ADDV    t5, acc6, acc6

    ADDV    t2, acc3, acc3
    SGTU    t2, acc3, t2
    ADDV    t1, acc3, acc3
    SGTU    t1, acc3, t1
    OR      t2, t1, t1
    ADDV    t4, acc4, acc4
    SGTU    t4, acc4, t4
    ADDV    t3, acc4, acc4
    SGTU    t3, acc4, t3
    OR      t4, t3, t3
    ADDV    t1, acc4, acc4
    SGTU    t1, acc4, t1
    OR      t3, t1, t1
    ADDV    t1, acc6, acc6

    // ---- 第三次约简 ----
    SLLV    $32, acc2, t2
    SRLV    $32, acc2, t0
    MOVV    p256const1<>(SB), t6
    MULV    acc2, t6, t1
    MULHVU  acc2, t6, acc2

    ADDV    t2, acc3, acc3
    SGTU    t2, acc3, t3
    ADDV    t0, acc0, acc0
    SGTU    t0, acc0, t4
    ADDV    t3, acc0, acc0
    SGTU    t3, acc0, t3
    OR      t4, t3, t3
    ADDV    t1, acc1, acc1
    SGTU    t1, acc1, t4
    ADDV    t3, acc1, acc1
    SGTU    t3, acc1, t3
    OR      t4, t3, t3
    ADDV    t3, acc2, acc2

    // ==================== y3 * x ====================
    MULV    y3, x0, t0
    ADDV    t0, acc3, acc3
    SGTU    t0, acc3, t1
    MULHVU  y3, x0, t2

    MULV    y3, x1, t0
    ADDV    t0, acc4, acc4
    SGTU    t0, acc4, t3
    MULHVU  y3, x1, t4

    MULV    y3, x2, t0
    ADDV    t0, acc5, acc5
    SGTU    t0, acc5, t5
    MULHVU  y3, x2, acc6
    ADDV    t5, acc6, acc6

    MULV    y3, x3, t0
    ADDV    t0, acc6, acc6
    SGTU    t0, acc6, t5
    MULHVU  y3, x3, acc7
    ADDV    t5, acc7, acc7

    ADDV    t2, acc4, acc4
    SGTU    t2, acc4, t2
    ADDV    t1, acc4, acc4
    SGTU    t1, acc4, t1
    OR      t2, t1, t1
    ADDV    t4, acc5, acc5
    SGTU    t4, acc5, t4
    ADDV    t3, acc5, acc5
    SGTU    t3, acc5, t3
    OR      t4, t3, t3
    ADDV    t1, acc5, acc5
    SGTU    t1, acc5, t1
    OR      t3, t1, t1
    ADDV    t1, acc7, acc7

    // ---- 第四次约简 ----
    SLLV    $32, acc3, t2
    SRLV    $32, acc3, t0
    MOVV    p256const1<>(SB), t6
    MULV    acc3, t6, t1
    MULHVU  acc3, t6, acc3

    ADDV    t2, acc0, acc0
    SGTU    t2, acc0, t3
    ADDV    t0, acc1, acc1
    SGTU    t0, acc1, t4
    ADDV    t3, acc1, acc1
    SGTU    t3, acc1, t3
    OR      t4, t3, t3
    ADDV    t1, acc2, acc2
    SGTU    t1, acc2, t4
    ADDV    t3, acc2, acc2
    SGTU    t3, acc2, t3
    OR      t4, t3, t3
    ADDV    t3, acc3, acc3

    // ==================== 合并高位 [511:256] ====================
    ADDV    acc4, acc0, acc0
    SGTU    acc4, acc0, t0
    ADDV    acc5, acc1, acc1
    SGTU    acc5, acc1, t1
    ADDV    t0, acc1, acc1
    SGTU    t0, acc1, t0
    OR      t1, t0, t0

    ADDV    acc6, acc2, acc2
    SGTU    acc6, acc2, t1
    ADDV    t0, acc2, acc2
    SGTU    t0, acc2, t0
    OR      t1, t0, t0

    ADDV    acc7, acc3, acc3
    SGTU    acc7, acc3, t1
    ADDV    t0, acc3, acc3
    SGTU    t0, acc3, t0
    OR      t1, t0, t0

    MOVV    t0, acc4            // 最终溢出标志 (0 或 1)

    // ==================== 条件减法 p（使用位掩码选择） ====================
    // 计算借位
    MOVV    $-1, t6
    SGTU    t6, acc0, t5        // borrow0 = 1 if acc0 < 0xFFFFFFFFFFFFFFFF
    ADDV    $1, acc0, t0        // d0 = acc0 + 1

    MOVV    p256const0<>(SB), t6
    SUBV    t6, acc1, t1
    SGTU    t6, acc1, t4
    MOVV    t1, t6
    SUBV    t5, t1, t1
    SGTU    t1, t6, t6
    OR      t4, t6, t5          // borrow1

    SUBV    $0, acc2, t2
    SGTU    $0, acc2, t4        // 恒0
    MOVV    t2, t6
    SUBV    t5, t2, t2
    SGTU    t2, t6, t6
    OR      t4, t6, t5

    MOVV    p256const1<>(SB), t6
    SUBV    t6, acc3, t3
    SGTU    t6, acc3, t4
    MOVV    t3, t6
    SUBV    t5, t3, t3
    SGTU    t3, t6, t6
    OR      t4, t6, t5          // 最终借位 t5 (0 或 1)

    // 将 acc4（额外溢出 limb）纳入借位链：acc4 -= borrow(acc0..acc3)
    // 若 acc4=1 且未借位(t5=0) -> acc4 变为 1，仍需减 P（一定溢出）
    // 若 acc4=0 且借位(t5=1)   -> acc4 变为 -1，说明原值 < P，不应减
    // 若 acc4=1 且借位(t5=1)   -> acc4 变为 0，恰好抵消，需要减 P
    // 若 acc4=0 且未借位(t5=0) -> acc4 保持 0，需要减 P
    SUBV    t5, acc4, acc4

    // mask: acc4>=0（即符号位为0，表示整条链无借位）-> 选减法结果 t0..t3
    //       acc4<0（符号位为1，表示确实小于 P）      -> 选原始 acc0..acc3
    SRAV    $63, acc4, t5
    MOVV    $-1, t6
    XOR     t5, t6, t6          // t6 = ~t5  

    // 选择：若借位为0（无借位，acc >= p）取减后值 t0..t3
    //       若借位为1（有借位，acc < p）取原值 acc0..acc3
    AND     t6, t0, t4
    AND     t5, acc0, t5
    OR      t4, t5, y0

    AND     t6, t1, t4
    AND     t5, acc1, t5
    OR      t4, t5, y1

    AND     t6, t2, t4
    AND     t5, acc2, t5
    OR      t4, t5, y2

    AND     t6, t3, t4
    AND     t5, acc3, t5
    OR      t4, t5, y3

    RET


// func p256Mul(res, in1, in2 *p256Element)  
TEXT ·p256Mul(SB),NOSPLIT,$0 
	MOVV	res+0(FP), res_ptr  
	MOVV	in1+8(FP), a_ptr  
	MOVV	in2+16(FP), b_ptr  
  
	MOVV	0*8(a_ptr), x0  
	MOVV	1*8(a_ptr), x1  
	MOVV	2*8(a_ptr), x2  
	MOVV	3*8(a_ptr), x3  
  
	MOVV	0*8(b_ptr), y0  
	MOVV	1*8(b_ptr), y1  
	MOVV	2*8(b_ptr), y2  
	MOVV	3*8(b_ptr), y3  
  
	CALL	p256MulInternal<>(SB)  
  
	MOVV	y0, 0*8(res_ptr)  
	MOVV	y1, 1*8(res_ptr)  
	MOVV	y2, 2*8(res_ptr)  
	MOVV	y3, 3*8(res_ptr)  
	RET

/* ---------------------------------------*/  
#define p256MulBy2Inline \
	/* x0..x3 = y0..y3 + y0..y3 (double), overflow bit -> hlp0 */ \
	ADDV	y0, y0, x0             ;\
	SGTU	y0, x0, t0              ;\
	\
	ADDV	y1, y1, t1              ;\
	SGTU	y1, t1, t2              ;\
	ADDV	t0, t1, x1              ;\
	SGTU	t0, x1, t3              ;\
	OR	t2, t3, t0              ;\
	\
	ADDV	y2, y2, t1              ;\
	SGTU	y2, t1, t2              ;\
	ADDV	t0, t1, x2              ;\
	SGTU	t0, x2, t3              ;\
	OR	t2, t3, t0              ;\
	\
	ADDV	y3, y3, t1              ;\
	SGTU	y3, t1, t2              ;\
	ADDV	t0, t1, x3              ;\
	SGTU	t0, x3, t3              ;\
	OR	t2, t3, hlp0            ;\
	\
	/* t0..t3 = x0..x3 - P (4-limb borrow chain, same pattern validated in p256MulInternal) */ \
	MOVV	$-1, t6                 ;\
	SGTU	t6, x0, t5              ;\
	ADDV	$1, x0, t0              ;\
	\
	MOVV	p256const0<>(SB), t5	;\
	SUBV	t5, x1, t1	        ;\
	SGTU	t5, x1, t4              ;\
	MOVV	t1, t6                  ;\
	SUBV	t5, t1, t1              ;\
	SGTU	t1, t6, t6              ;\
	OR	t4, t6, t5              ;\
	\
	SUBV	$0, x2, t2              ;\
	SGTU	$0, x2, t4              ;\
	MOVV	t2, t6                  ;\
	SUBV	t5, t2, t2              ;\
	SGTU	t2, t6, t6              ;\
	OR	t4, t6, t5              ;\
	\
	MOVV	p256const1<>(SB), t6	;\
	SUBV	t6, x3, t3              ;\
	SGTU	t6, x3, t4              ;\
	MOVV	t3, t6                  ;\
	SUBV	t5, t3, t3              ;\
	SGTU	t3, t6, t6              ;\
	OR	t4, t6, t5              ;\
	\
	/* fold doubling-overflow bit into the borrow chain */ \
	SUBV	t5, hlp0, hlp0          ;\
	SRAV	$63, hlp0, t5           ;\
	MOVV	$-1, t6                 ;\
	XOR	t5, t6, t6              ;\
	\
	/* select: no-borrow (>= P) -> t0..t3 ; borrow (< P) -> original x0..x3 */ \
	AND	t6, t0, t4              ;\
	AND	t5, x0, hlp0            ;\
	OR	t4, hlp0, x0            ;\
	\
	AND	t6, t1, t4              ;\
	AND	t5, x1, hlp0            ;\
	OR	t4, hlp0, x1            ;\
	\
	AND	t6, t2, t4              ;\
	AND	t5, x2, hlp0            ;\
	OR	t4, hlp0, x2            ;\
	\
	AND	t6, t3, t4              ;\
	AND	t5, x3, hlp0            ;\
	OR	t4, hlp0, x3            ;

/* ---------------------------------------*/  
#define y2in(off)  (8 + 32*0 + off)(R3)  
#define s2v(off)   (8 + 32*1 + off)(R3)  
#define z1sqr(off) (8 + 32*2 + off)(R3)  
#define hv(off)    (8 + 32*3 + off)(R3)  
#define rv(off)    (8 + 32*4 + off)(R3)  
#define hsqr(off)  (8 + 32*5 + off)(R3)  
#define rsqr(off)  (8 + 32*6 + off)(R3)  
#define hcub(off)  (8 + 32*7 + off)(R3)  

/*
 * slot 8:
 *  +0 : sel | (zero << 1)
 *  +8 : normalized sign
 *
 * Both values need to survive CALLs, so keep them on the stack.
 */
#define flagbase(off)	(8 + 32*8 + off)(R3)
#define selflag(off)	flagbase(off)
#define signflag(off)	flagbase(8 + off)

//// PointAdd temporary spill slots.
//// x3/y2/y3 use R9/R2/R31 and must not be relied on across CALL.
//#define x3save(off) (8 + 32*9 + off)(R3)
//#define y2save(off) (8 + 32*10 + off)(R3)
//#define y3save(off) (8 + 32*11 + off)(R3)
  
#define x1in(off) (off)(a_ptr)  
#define y1in(off) (off+32)(a_ptr)  
#define z1in(off) (off+64)(a_ptr)  
#define x2in(off) (off)(b_ptr)  
#define z2in(off) (off + 64)(b_ptr)
#define x3out(off) (off)(res_ptr)
#define y3out(off) (off + 32)(res_ptr)
#define z3out(off) (off + 64)(res_ptr)
#define y2inptr(off) (off+32)(b_ptr)  
  
#define LDx(src) \
	MOVV src(0*8),x0; \
	MOVV src(1*8),x1; \
	MOVV src(2*8),x2; \
	MOVV src(3*8),x3

#define LDy(src) \
	MOVV src(0*8),y0; \
	MOVV src(1*8),t4; \
	MOVV src(2*8),y2; \
	MOVV src(3*8),y3; \
	MOVV t4, y1

#define STx(dst) MOVV x0,dst(0*8); MOVV x1,dst(1*8); MOVV x2,dst(2*8); MOVV x3,dst(3*8)  
#define STy(dst) MOVV y0,dst(0*8); MOVV y1,dst(1*8); MOVV y2,dst(2*8); MOVV y3,dst(3*8)  

#define RELOAD_PTRS \
	MOVV	in1+8(FP), a_ptr ;\
	MOVV	in2+16(FP), b_ptr

// func p256PointAddAffineAsm(res, in1 *P256Point, in2 *p256AffinePoint, sign, sel, zero int)  
TEXT ·p256PointAddAffineAsm(SB),NOSPLIT,$352-48  
	// sign/sel/zero 不能借用 hlp0(=b_ptr)/y1(=a_ptr)，先用 t5/t6 承接  
	MOVV	sign+24(FP), t5      // t5 = sign  
	MOVV	sel+32(FP), t6       // t6 = sel  
	MOVV	zero+40(FP), t0      // t0 = zero  
  
	// 规整 sel/zero 为 0/1，再合并成 hlp1 语义（这里直接用 t1 保存合并结果）  
	SGTU	t6, R0, t2           // t2 = (sel != 0) ? 1 : 0  
	SGTU	t0, R0, t3           // t3 = (zero != 0) ? 1 : 0  
	SLLV	$1, t3, t3  
	XOR	t2, t3, t1           // t1 = sel_norm ^ (zero_norm<<1)，后续用它做位测试  
	MOVV    t1, selflag(0)       // 立即存回栈，不依赖寄存器跨越多次CALL存活
  
	// sign 规整为 0/1，存入 t4（供后面条件选择使用）  
	SGTU	t5, R0, t4  
	MOVV	t4, signflag(0)		// sign 需要跨越后面的CALL， 立即保存到栈
  
	RELOAD_PTRS                 // 确保 a_ptr/b_ptr 干净  
  
  	// ---- Negate y2in based on sign: compute P - y2in via p256SubInternal ----
	// p256SubInternal computes diff = y - x (result in x0..x3), so:
	//   x0..x3 = y2in (value to subtract)
	//   y0..y3 = P
	MOVV	y2inptr(0*8), x0
	MOVV	y2inptr(1*8), x1
	MOVV	y2inptr(2*8), x2
	MOVV	y2inptr(3*8), x3

	MOVV	$-1, y0
	MOVV	p256const0<>(SB), y1
	MOVV	$0, y2
	MOVV	p256const1<>(SB), y3

	CALL	p256SubInternal<>(SB)   // x0..x3 = P - y2in
	RELOAD_PTRS                    // a_ptr/b_ptr(=hlp0)/y1 clobbered by the call

	// reload original y2in (y0..y3 were consumed as the P operand above)
	MOVV	y2inptr(0*8), y0
	MOVV	y2inptr(1*8), y1
	MOVV	y2inptr(2*8), y2
	MOVV	y2inptr(3*8), y3

	// Restore normalized sign from the stack.
	// mask = 0 (sign==0, keep original) or all-ones (sign!=0, use negated)
	MOVV	signflag(0), t4		// 从栈恢复 normalized sign
	SUBV	t4, R0, t2		// t2 = mask
	MOVV	$-1, t3
	XOR	t2, t3, t3               // t3 = notmask

	AND	t3, y0, acc0
	AND	t2, x0, acc4
	OR	acc0, acc4, y0

	AND	t3, y1, acc0
	AND	t2, x1, acc4
	OR	acc0, acc4, y1

	AND	t3, y2, acc0
	AND	t2, x2, acc4
	OR	acc0, acc4, y2

	AND	t3, y3, acc0
	AND	t2, x3, acc4
	OR	acc0, acc4, y3

	STy(y2in)
  
	// ---- Begin point add ----  
	RELOAD_PTRS

	LDx(z1in)  
	CALL	p256SqrInternal<>(SB)    // z1^2  —— 调用后 a_ptr/b_ptr(=hlp0)/y1 已被污染  
	STy(z1sqr)  
	RELOAD_PTRS                     // 策略3：立即重新加载  
  
	LDx(x2in)  
	CALL	p256MulInternal<>(SB)    // u2 = x2 * z1^2  
	MOVV	y0, rsqr(0*8)
	MOVV	y1, rsqr(1*8)
	MOVV	y2, rsqr(2*8)
	MOVV	y3, rsqr(3*8)
	RELOAD_PTRS  
  
	LDx(x1in)  
	LDy(rsqr)
	CALL	p256SubInternal<>(SB)    // h = u2 - x1  
	STx(hv)  
	RELOAD_PTRS  
  
	LDy(z1in)  
	CALL	p256MulInternal<>(SB)    // z3 = h * z1  
	STy(s2v)
	RELOAD_PTRS  

	// p256MulInternal 会破坏 a_ptr/b_ptr/y1, 因此必须在 PELOAD_PTRS之后重新加载z3
	MOVV	s2v(0*8), y0
	MOVV	s2v(1*8), t4
	MOVV	s2v(2*8), y2
	MOVV	s2v(3*8), y3
	MOVV	t4, y1
  
	// 条件覆盖 z3: 位0为0->z1; 位1为0->1  
	MOVV	z1in(0*8), acc0  
	MOVV	z1in(1*8), acc1  
	MOVV	z1in(2*8), acc2  
	MOVV	z1in(3*8), acc3  
	MOVV    selflag(0), t1       // 重新加载位掩码，t1可能已被内部函数调用覆写
        AND     $1, t1, t2  
	SUBV	$0, t2, t2               // 0/1 -> 0/全1掩码  
	MOVV	$-1, t3  
	XOR	t2, t3, t3               // t3 = ~mask  
	AND	t3, y0, y0; AND t2, acc0, acc0; OR y0, acc0, y0  
	AND	t3, y1, y1; AND t2, acc1, acc1; OR y1, acc1, y1  
	AND	t3, y2, y2; AND t2, acc2, acc2; OR y2, acc2, y2  
	AND	t3, y3, y3; AND t2, acc3, acc3; OR y3, acc3, y3  
  
	MOVV	p256one<>+0x00(SB), acc0  
	MOVV	p256one<>+0x08(SB), acc1  
	MOVV	p256one<>+0x10(SB), acc2  
	MOVV	p256one<>+0x18(SB), acc3  
	MOVV    selflag(0), t1
	AND	$2, t1, t2  
	SRLV	$1, t2, t2  
	SUBV	$0, t2, t2  
	MOVV	$-1, t3  
	XOR	t2, t3, t3  
	AND	t3, y0, y0; AND t2, acc0, acc0; OR y0, acc0, y0  
	AND	t3, y1, y1; AND t2, acc1, acc1; OR y1, acc1, y1  
	AND	t3, y2, y2; AND t2, acc2, acc2; OR y2, acc2, y2  
	AND	t3, y3, y3; AND t2, acc3, acc3; OR y3, acc3, y3  
  
	// Save the selected z3 before loading the next temporary.
	MOVV	res+0(FP), t0
	MOVV	y0, 4*8(t0)
	MOVV	y1, 5*8(t0)
	MOVV	y2, 6*8(t0)
	MOVV	y3, 7*8(t0)

	LDy(z1sqr)  
	CALL	p256MulInternal<>(SB)    // z1^3  
	MOVV	y0, rsqr(0*8)
	MOVV	y1, rsqr(1*8)
	MOVV	y2, rsqr(2*8)
	MOVV	y3, rsqr(3*8)
	RELOAD_PTRS  
  
	LDx(y2in)  
	LDy(rsqr)
	CALL	p256MulInternal<>(SB)    // s2 = y2in * z1^3  
	STy(s2v)  
	RELOAD_PTRS  
  
	LDx(y1in)  
	CALL	p256SubInternal<>(SB)    // r = s2 - y1  
	STx(rv)  
	RELOAD_PTRS  
  
	CALL	p256SqrInternal<>(SB)    // rsqr = r^2  
	STy(rsqr)  
	RELOAD_PTRS  
  
	LDx(hv)  
	CALL	p256SqrInternal<>(SB)    // hsqr = h^2  
	STy(hsqr)  
	RELOAD_PTRS  
  
	CALL	p256MulInternal<>(SB)    // hcub = h^3  
	STy(hcub)  
	RELOAD_PTRS  
  
	LDx(y1in)  
	CALL	p256MulInternal<>(SB)    // s2' = y1 * hcub  
	STy(s2v)  
	RELOAD_PTRS  
  
	MOVV	hsqr(0*8), x0  
	MOVV	hsqr(1*8), x1  
	MOVV	hsqr(2*8), x2  
	MOVV	hsqr(3*8), x3  
	MOVV	x1in(0*8), y0  
	MOVV	x1in(1*8), y1  
	MOVV	x1in(2*8), y2  
	MOVV	x1in(3*8), y3  
	CALL	p256MulInternal<>(SB)    // u1' = x1 * hsqr  
	STy(hv)                          // 覆盖存栈 h  
	RELOAD_PTRS  
  
	p256MulBy2Inline                 // u1'2 = 2*u1' (x0..x3 -> 已在寄存器中)  
  
	LDy(rsqr)  
	CALL	p256SubInternal<>(SB)    // rsqr - u1'2  
	RELOAD_PTRS  
  
	MOVV	x0, y0  
	MOVV	x1, y1  
	MOVV	x2, y2  
	MOVV	x3, y3  

	LDx(hcub)  
	CALL	p256SubInternal<>(SB)   // x3 = 上一步结果 - hcub  
	RELOAD_PTRS  
  
	// 条件覆盖 x3  
	MOVV	x1in(0*8), acc0  
	MOVV	x1in(1*8), acc1  
	MOVV	x1in(2*8), acc2  
	MOVV	x1in(3*8), acc3  
	MOVV    selflag(0), t1
	AND	$1, t1, t2  
	SUBV	$0, t2, t2  
	MOVV	$-1, t3  
	XOR	t2, t3, t3  
	AND	t3, x0, x0; AND t2, acc0, acc0; OR x0, acc0, x0  
	AND	t3, x1, x1; AND t2, acc1, acc1; OR x1, acc1, x1  
	AND	t3, x2, x2; AND t2, acc2, acc2; OR x2, acc2, x2  
	AND	t3, x3, x3; AND t2, acc3, acc3; OR x3, acc3, x3  
  
	MOVV	x2in(0*8), acc0  
	MOVV	x2in(1*8), acc1  
	MOVV	x2in(2*8), acc2  
	MOVV	x2in(3*8), acc3  
	MOVV    selflag(0), t1
	AND	$2, t1, t2  
	SRLV	$1, t2, t2  
	SUBV	$0, t2, t2  
	MOVV	$-1, t3  
	XOR	t2, t3, t3  
	AND	t3, x0, x0; AND t2, acc0, acc0; OR x0, acc0, x0  
	AND	t3, x1, x1; AND t2, acc1, acc1; OR x1, acc1, x1  
	AND	t3, x2, x2; AND t2, acc2, acc2; OR x2, acc2, x2  
	AND	t3, x3, x3; AND t2, acc3, acc3; OR x3, acc3, x3  
  
	MOVV	res+0(FP), t0  
	MOVV	x0, 0*8(t0)  
	MOVV	x1, 1*8(t0)  
	MOVV	x2, 2*8(t0)  
	MOVV	x3, 3*8(t0)  
  
  	MOVV	0*8(t0), x0
  	MOVV	1*8(t0), x1
  	MOVV	2*8(t0), x2
  	MOVV	3*8(t0), x3
	LDy(hv)                          // u1'  
	CALL	p256SubInternal<>(SB)    // tmp = u1' - x3  
	RELOAD_PTRS  
  
  	MOVV	rv(0*8), y0
  	MOVV	rv(1*8), y1
  	MOVV	rv(2*8), y2
  	MOVV	rv(3*8), y3
	CALL	p256MulInternal<>(SB)    // tmp2 = r * tmp  
	MOVV	y0, rv(0*8)
	MOVV	y1, rv(1*8)
	MOVV	y2, rv(2*8)
	MOVV	y3, rv(3*8)
	RELOAD_PTRS  
  
	LDx(s2v)  
	LDy(rv)
	CALL	p256SubInternal<>(SB)    // y3 = tmp2 - s2'  
	RELOAD_PTRS  
  
	// 条件覆盖 y3  
	MOVV	y1in(0*8), acc0  
	MOVV	y1in(1*8), acc1  
	MOVV	y1in(2*8), acc2  
	MOVV	y1in(3*8), acc3  
	MOVV    selflag(0), t1
	AND	$1, t1, t2  
	SUBV	$0, t2, t2  
	MOVV	$-1, t3  
	XOR	t2, t3, t3  
	AND	t3, x0, x0; AND t2, acc0, acc0; OR x0, acc0, x0  
	AND	t3, x1, x1; AND t2, acc1, acc1; OR x1, acc1, x1  
	AND	t3, x2, x2; AND t2, acc2, acc2; OR x2, acc2, x2  
	AND	t3, x3, x3; AND t2, acc3, acc3; OR x3, acc3, x3  
  
	MOVV	y2in(0*8), acc0  
	MOVV	y2in(1*8), acc1  
	MOVV	y2in(2*8), acc2  
	MOVV	y2in(3*8), acc3  
	MOVV    selflag(0), t1
	AND	$2, t1, t2  
	SRLV	$1, t2, t2  
	SUBV	$0, t2, t2  
	MOVV	$-1, t3  
	XOR	t2, t3, t3  
	AND	t3, x0, x0; AND t2, acc0, acc0; OR x0, acc0, x0  
	AND	t3, x1, x1; AND t2, acc1, acc1; OR x1, acc1, x1  
	AND	t3, x2, x2; AND t2, acc2, acc2; OR x2, acc2, x2  
	AND	t3, x3, x3; AND t2, acc3, acc3; OR x3, acc3, x3  
  
	MOVV	res+0(FP), t0  
	MOVV	x0, 4*8(t0)  
	MOVV	x1, 5*8(t0)  
	MOVV	x2, 6*8(t0)  
	MOVV	x3, 7*8(t0)  
  
	RET

// ---------------------------------------  
// PointDouble 专用栈变量（基于 SP 伪寄存器，避免与自动保存的 LR 冲突）  
#define zsqrv(off) (8 + 32*0 + off)(R3)  
#define mv(off)    (8 + 32*1 + off)(R3)  
#define h2v(off)   (8 + 32*2 + off)(R3)  
#define sv(off)    (8 + 32*3 + off)(R3)  
#define tmpv(off)  (8 + 32*4 + off)(R3)  
#define y3tmp(off) (8 + 32*5 + off)(R3)  
  
#define RELOAD_A \  
	MOVV	in1+8(FP), a_ptr  
  
// ---- 模P半减：y0..y3 = (y0..y3) / 2 mod P ----  
// 若为偶数直接右移1位；若为奇数先加P再右移1位  
#define p256HalveInline \  
	ADDV	$-1, y0, t0              ;\  
	SGTU	$-1, t0, t4              ;\  
	MOVV	p256const0<>(SB), t5	 ;\
	ADDV	t5, y1, t1               ;\  
	SGTU    t5, t1, t5               ;\
	ADDV	t4, t1, t1               ;\  
	SGTU    t4, t1, t6               ;\ 
	OR	t5, t6, t4               ;\  
	ADDV	$0, y2, t2               ;\  
	ADDV	t4, t2, t2               ;\  
	SGTU	t4, t2, t4               ;\  
	MOVV	p256const1<>(SB), t5	 ;\
	ADDV	t5, y3, t3               ;\  
	SGTU    t5, t3, t5               ;\
	ADDV	t4, t3, t3               ;\  
	SGTU    t4, t3, t6               ;\
	OR	t5, t6, hlp0             ;\  
	\  
	AND	$1, y0, t4               ;\  
	SUBV	$0, t4, t4               ;\ /* t4 = 0(偶数)/全1(奇数) */  
	MOVV	$-1, t5                  ;\  
	XOR	t4, t5, t5               ;\ /* t5 = notmask */  
	AND	t5, y0, acc0; AND t4, t0, acc4; OR acc0, acc4, t0 ;\  
	AND	t5, y1, acc0; AND t4, t1, acc4; OR acc0, acc4, t1 ;\  
	AND	t5, y2, acc0; AND t4, t2, acc4; OR acc0, acc4, t2 ;\  
	AND	t5, y3, acc0; AND t4, t3, acc4; OR acc0, acc4, t3 ;\  
	AND	t4, hlp0, hlp0           ;\  
	\  
	SRLV	$1, t0, y0               ;\  
	SLLV	$63, t1, acc0            ;\  
	OR	acc0, y0, y0             ;\  
	SRLV	$1, t1, y1               ;\  
	SLLV	$63, t2, acc0            ;\  
	OR	acc0, y1, y1             ;\  
	SRLV	$1, t2, y2               ;\  
	SLLV	$63, t3, acc0            ;\  
	OR	acc0, y2, y2             ;\  
	SRLV	$1, t3, y3               ;\  
	SLLV	$63, hlp0, acc0          ;\  
	OR	acc0, y3, y3

// x = (x + y) mod P，结果原地写回 x0..x3  
// y0..y3 会被读取但不会被写；调用后 y0..y3 内容仍是原值  
#define p256AddInline                 \  
	ADDV	y0, x0, x0            ;\  
	SGTU	y0, x0, hlp0           ;\ /* hlp0 = limb0 进位 */  
	ADDV	y1, x1, x1            ;\  
	SGTU	y1, x1, t4             ;\  
	ADDV	hlp0, x1, x1           ;\  
	SGTU	hlp0, x1, t5           ;\  
	OR	t4, t5, hlp0           ;\  
	ADDV	y2, x2, x2            ;\  
	SGTU	y2, x2, t4             ;\  
	ADDV	hlp0, x2, x2           ;\  
	SGTU	hlp0, x2, t5           ;\  
	OR	t4, t5, hlp0           ;\  
	ADDV	y3, x3, x3            ;\  
	SGTU	y3, x3, t4             ;\  
	ADDV	hlp0, x3, x3           ;\  
	SGTU	hlp0, x3, t5           ;\  
	OR	t4, t5, hlp0           ;\ /* hlp0 = 最终溢出位 (0/1)，1 表示 x+y>=2^256 */  
	\  
	SUBV	$-1, x0, t0            ;\ /* t0 = x0 - P0  (P0 = -1，即 0xFFFF...FFFF) */  
	SGTU	$-1, x0, t4            ;\ /* t4 = borrow0 = (x0 < P0) */  
	MOVV	p256const0<>(SB), t5   ;\
	SUBV	t5, x1, t1             ;\  
	SGTU	t5, x1, t5             ;\  
	SUBV	t4, t1, t1             ;\  
	SGTU	t4, t1, t6             ;\  
	OR	t5, t6, t4             ;\  
	SUBV	$0, x2, t2             ;\  
	SGTU	$0, x2, t5             ;\  
	SUBV	t4, t2, t2             ;\  
	SGTU	t4, t2, t6             ;\  
	OR	t5, t6, t4             ;\  
	MOVV	p256const1<>(SB), t5   ;\
	SUBV	t5, x3, t3             ;\  
	SGTU	t5, x3, t5             ;\  
	SUBV	t4, t3, t3             ;\  
	SGTU	t4, t3, t6             ;\  
	OR	t5, t6, t4             ;\ /* t4 = 4-limb 借位 (1 表示 x < P，无需减) */  
	\  
	SUBV	t4, hlp0, hlp0         ;\ /* hlp0 - t4：结果为 1/0（需要减）或 -1（不需要减） */  
	SRAV	$63, hlp0, t5          ;\ /* t5 = 全1(不需要减) 或 全0(需要减) */  
	MOVV	$-1, t6                ;\  
	XOR	t5, t6, t6             ;\ /* t6 = notmask：全1(需要减) 或 全0(不需要减) */  
	\  
	AND	t6, t0, hlp0           ;\  
	AND	t5, x0, x0             ;\  
	OR	hlp0, x0, x0           ;\  
	AND	t6, t1, hlp0           ;\  
	AND	t5, x1, x1             ;\  
	OR	hlp0, x1, x1           ;\  
	AND	t6, t2, hlp0           ;\  
	AND	t5, x2, x2             ;\  
	OR	hlp0, x2, x2           ;\  
	AND	t6, t3, hlp0           ;\  
	AND	t5, x3, x3             ;\  
	OR	hlp0, x3, x3

// func p256PointDoubleAsm(res, in *P256Point)  
TEXT ·p256PointDoubleAsm(SB),NOSPLIT,$192-16  
	MOVV	res+0(FP), res_ptr  
	MOVV	in+8(FP), a_ptr  
  
	// zsqr = Z1^2  
	LDx(z1in)  
	CALL	p256SqrInternal<>(SB)  
	STy(zsqrv)  
	RELOAD_A  
  
	// m_pre = X1 + zsqr  (x = X1, y = zsqr)  
	LDx(x1in)  
	LDy(zsqrv)  
	p256AddInline               // x0..x3 = x + y = X1 + zsqr  
	STx(mv)                     // 先把 m_pre 存起来，后面还要复用 x1in/zsqr  
  
	// z3 = 2*(Y1*Z1) -> res.z  
	LDx(z1in)  
	LDy(y1in)  
	CALL	p256MulInternal<>(SB)  
	RELOAD_A  
	MOVV	y0, x0  
	MOVV	y1, x1  
	MOVV	y2, x2  
	MOVV	y3, x3  
	p256MulBy2Inline  
	STx(z3out)  
  
	// h = X1 - zsqr  (p256SubInternal: diff = y - x, 故 y=X1, x=zsqr)  
	LDy(x1in)  
	LDx(zsqrv)  
	CALL	p256SubInternal<>(SB)  
	RELOAD_A  
  
	// h2 = h * m_pre  
	MOVV	x0, y0  
	MOVV	x1, y1  
	MOVV	x2, y2  
	MOVV	x3, y3  
	LDx(mv)  
	CALL	p256MulInternal<>(SB)  
	RELOAD_A  
	STy(h2v)                    // 关键修正：先保存一份原始 h2，避免被下面的 MulBy2 覆盖丢失  
  
	// M = 3*h2 = 2*h2 + h2  
	MOVV	y0, x0  
	MOVV	y1, x1  
	MOVV	y2, x2  
	MOVV	y3, x3  
	p256MulBy2Inline             // x0..x3 = 2*h2  
	LDy(h2v)                     // y0..y3 = 原始 h2（未被覆盖）  
	p256AddInline                // x0..x3 = 2*h2 + h2 = 3*h2 = M  
	STx(mv)                      // 覆盖存回 m  
  
	// s = (2*Y1)^2 = 4*Y1^2  
	LDx(y1in)  
	MOVV	x0, y0  
	MOVV	x1, y1  
	MOVV	x2, y2  
	MOVV	x3, y3  
	p256MulBy2Inline             // x0..x3 = 2*Y1  
	MOVV	x0, y0  
	MOVV	x1, y1  
	MOVV	x2, y2  
	MOVV	x3, y3  
	CALL	p256SqrInternal<>(SB) // y0..y3 = (2*Y1)^2 = s  
	RELOAD_A  
	STy(sv)  
  
	// yyyy = s^2 = 16*Y1^4  
	MOVV	y0, x0  
	MOVV	y1, x1  
	MOVV	y2, x2  
	MOVV	y3, x3  
	CALL	p256SqrInternal<>(SB) // y0..y3 = s^2 = 16*Y1^4  
	RELOAD_A  
  
	// 8*Y1^4 = yyyy / 2 (mod P halving)  
	p256HalveInline               // y0..y3 = yyyy/2  
	STy(y3tmp)                    // 暂存，后面 Y3 计算要用  
  
	// S = X1 * s = 4*X1*Y1^2  
	LDx(x1in)  
	LDy(sv)  
	CALL	p256MulInternal<>(SB)  
	RELOAD_A  
	STy(sv)                       // 覆盖存回 s = S  
  
	// 2S = 8*X1*Y1^2  
	MOVV	y0, x0  
	MOVV	y1, x1  
	MOVV	y2, x2  
	MOVV	y3, x3  
	p256MulBy2Inline  
	STx(tmpv)                     // tmp = 2S  
  
	// Msqr = M^2  
	LDx(mv)  
	MOVV	x0, y0  
	MOVV	x1, y1  
	MOVV	x2, y2  
	MOVV	x3, y3  
	CALL	p256SqrInternal<>(SB) // y0..y3 = M^2  
	RELOAD_A  
  
	// X3 = Msqr - 2S  (diff = y - x, y = Msqr, x = 2S)  
	LDx(tmpv)  
	CALL	p256SubInternal<>(SB)  
	RELOAD_A  
	STx(x3out)                    // 写 res.x  
  
	// S - X3  (diff = y - x, y = S, x = X3)  
	LDy(sv)  
	CALL	p256SubInternal<>(SB)  
	RELOAD_A  
  
	// M * (S - X3)  
	MOVV	x0, y0  
	MOVV	x1, y1  
	MOVV	x2, y2  
	MOVV	x3, y3  
	LDx(mv)  
	CALL	p256MulInternal<>(SB)  
	RELOAD_A  
  
	// Y3 = M*(S-X3) - 8*Y1^4  (diff = y - x, y = 上一步结果, x = y3tmp)  
	MOVV	y0, y0  
	LDx(y3tmp)  
	CALL	p256SubInternal<>(SB)  
	RELOAD_A  
	STx(y3out)                    // 写 res.y  
  
	RET

/* ---------------------------------------*/
#undef y2in
#undef x3out
#undef y3out
#undef z3out
#define y2in(off) (off + 32)(b_ptr)
#define x3out(off) (off)(b_ptr)
#define y3out(off) (off + 32)(b_ptr)
#define z3out(off) (off + 64)(b_ptr)

// ---------------------------------------  
// p256PointAddAsm 专用栈变量（基于 SP 伪寄存器）  
#define z2sqrv(off)  (8 + 32*0  + off)(R3)  
#define s1v(off)     (8 + 32*1  + off)(R3)  
#define z1sqrv(off)  (8 + 32*2  + off)(R3)  
#define rv2(off)     (8 + 32*3  + off)(R3)   // r  
#define u1v(off)     (8 + 32*4  + off)(R3)  
#define u2v(off)     (8 + 32*5  + off)(R3)  
#define hsqrv(off)   (8 + 32*6  + off)(R3)  
#define rsqrv(off)   (8 + 32*7  + off)(R3)  
#define hcubv(off)   (8 + 32*8  + off)(R3)  
#define s2v2(off)    (8 + 32*9  + off)(R3)   // s2  
#define hv2(off)     (8 + 32*10 + off)(R3)   // h  
#define degflag(off) (8 + 32*11 + off)(R3)   // 退化点标志（仅用8字节）  
  
// y2in 仅在 b_ptr 仍指向 in2 时有效  
#define y2inp(off) (off+32)(b_ptr)  
  
//#define RELOAD_AB \  
//	MOVV	in1+8(FP), a_ptr ;\  
//	MOVV	in2+16(FP), b_ptr  
  
// ---------------------------------------  
// func p256PointAddAsm(res, in1, in2 *P256Point) int  
TEXT ·p256PointAddAsm(SB),0,$392-32  
	MOVV	in1+8(FP), a_ptr  
	MOVV	in2+16(FP), b_ptr  
  
	// ---- z2sqr = Z2^2 ----  
	LDx(z2in)  
	CALL	p256SqrInternal<>(SB)  
	STy(z2sqrv)  
  
	// ---- z2cub = z2sqr * Z2 ----  
	MOVV	y0, x0  
	MOVV	y1, x1  
	MOVV	y2, x2  
	MOVV	y3, x3  
	RELOAD_PTRS
	LDy(z2in)  
	CALL	p256MulInternal<>(SB)  
  
	// ---- s1 = z2cub * Y1 ----  
	MOVV	y0, x0  
	MOVV	y1, x1  
	MOVV	y2, x2  
	MOVV	y3, x3  
	RELOAD_PTRS
	LDy(y1in)  
	CALL	p256MulInternal<>(SB)  
	STy(s1v)  
	RELOAD_PTRS
  
	// ---- z1sqr = Z1^2 ----  
	LDx(z1in)  
	CALL	p256SqrInternal<>(SB)  
	STy(z1sqrv)  
	RELOAD_PTRS
  
	// ---- z1cub = z1sqr * Z1 ----  
	LDx(z1sqrv)
	LDy(z1in)
	CALL	p256MulInternal<>(SB)  
  
	// ---- s2 = z1cub * Y2 ----  
	MOVV	y0, x0  
	MOVV	y1, x1  
	MOVV	y2, x2  
	MOVV	y3, x3  
	RELOAD_PTRS
	LDy(y2in)  
	CALL	p256MulInternal<>(SB)  
  
	// ---- r = s2 - s1  (diff = y - x, y = s2, x = s1) ----  
	LDx(s1v)  
	CALL	p256SubInternal<>(SB)  
	STx(rv2)  
  
	// ---- 检测 r == 0 mod P (r==0 或 r==P) ----  
	MOVV	$1, t2  
	OR	x0, x1, t0  
	OR	x2, x3, t1  
	OR	t1, t0, t0  
	SGTU	t0, R0, t1        // t1 = (t0 != 0) => 1 表示非零  
	XOR	$1, t1, t1         // t1 = (t0 == 0) => 1 表示 r==0  
	AND	t1, t2, hlp1        // hlp1 = r==0 ? 1 : 0 (临时，稍后立即落栈)  
  
	XOR	$-1, x0, t0  
	MOVV	p256const0<>(SB), t5
	XOR	t5, x1, t1  
	MOVV	p256const1<>(SB), t6
	XOR	t6, x3, t3  
	OR	t0, t1, t0  
	OR	x2, t3, t1  
	OR	t1, t0, t0  
	SGTU	t0, R0, t1  
	XOR	$1, t1, t1          // t1 = (r == P) => 1  
	OR	t1, hlp1, hlp1       // hlp1 = (r==0) OR (r==P)  
  
	MOVV	hlp1, degflag(0)    // 立即落栈，避免后续 CALL 污染  
  
	// ---- u1 = X1 * z2sqr ----  
	LDx(x1in)  
	LDy(z2sqrv)  
	CALL	p256MulInternal<>(SB)  
	STy(u1v)  
	RELOAD_PTRS
  
	// ---- u2 = X2 * z1sqr ----  
	LDx(x2in)  
	LDy(z1sqrv)  
	CALL	p256MulInternal<>(SB)  
  
	// ---- h = u2 - u1  (diff = y - x, y = u2, x = u1) ----  
	LDx(u1v)  
	CALL	p256SubInternal<>(SB)  
	STx(hv2)  
  
	// ---- 检测 h == 0 mod P，并与 degflag 合并（AND：两者都退化才算真退化）----  
	MOVV	$1, t2  
	OR	x0, x1, t0  
	OR	x2, x3, t1  
	OR	t1, t0, t0  
	SGTU	t0, R0, t1  
	XOR	$1, t1, t1  
	AND	t1, t2, hlp0  
  
	XOR	$-1, x0, t0  
	MOVV	p256const0<>(SB), t5
	XOR	t5, x1, t1  
	MOVV	p256const1<>(SB), t6
	XOR	t6, x3, t3  
	OR	t0, t1, t0  
	OR	x2, t3, t1  
	OR	t1, t0, t0  
	SGTU	t0, R0, t1  
	XOR	$1, t1, t1  
	OR	t1, hlp0, hlp0        // hlp0 = (h==0) OR (h==P)  
  
	MOVV	degflag(0), t4  
	AND	hlp0, t4, t4  
	MOVV	t4, degflag(0)       // degflag = r退化 AND h退化  
  
	// ---- rsqr = r^2 ----  
	LDx(rv2)  
	CALL	p256SqrInternal<>(SB)  
	STy(rsqrv)  
	RELOAD_PTRS
  
	// ---- hsqr = h^2 ----  
	LDx(hv2)  
	CALL	p256SqrInternal<>(SB)  
	STy(hsqrv)  
	RELOAD_PTRS
  
	// ---- hcub = h * hsqr ----  
	LDx(hsqrv)
	LDy(hv2)  
	CALL	p256MulInternal<>(SB)  
	STy(hcubv)  
	RELOAD_PTRS
  
	// ---- s2' = s1 * hcub ----  
	LDx(s1v)  
	LDy(hcubv)
	CALL	p256MulInternal<>(SB)  
	STy(s2v2)  
	RELOAD_PTRS
  
	// ---- z3 = z1 * z2 * h ----  
	LDx(z1in)  
	LDy(z2in)  
	CALL	p256MulInternal<>(SB)  
	MOVV	y0, x0  
	MOVV	y1, x1  
	MOVV	y2, x2  
	MOVV	y3, x3  
	RELOAD_PTRS
	LDy(hv2)  
	CALL	p256MulInternal<>(SB)  
	MOVV	res+0(FP), b_ptr     // 从此处开始 b_ptr 改指向 res，之前依赖旧 b_ptr(in2) 的读取必须已全部完成  
	STy(z3out)  
  
	// ---- u2' = hsqr * u1 ----  
	LDx(hsqrv)  
	LDy(u1v)  
	CALL	p256MulInternal<>(SB)  
	STy(u2v)  
  
	// ---- tmp = 2 * u2' ----  
	p256MulBy2Inline  
	RELOAD_PTRS
  
	// ---- x3_0 = rsqr - tmp  (diff = y - x, y = rsqr, x = tmp) ----  
	LDy(rsqrv)  
	CALL	p256SubInternal<>(SB)  
	RELOAD_PTRS
	MOVV	res+0(FP), b_ptr  
  
	// ---- x3 = x3_0 - hcub ----  
	MOVV	x0, y0  
	MOVV	x1, y1  
	MOVV	x2, y2  
	MOVV	x3, y3  
	LDx(hcubv)  
	CALL	p256SubInternal<>(SB)  
	RELOAD_PTRS
	MOVV	res+0(FP), b_ptr  
	STx(x3out)  
  
	// ---- tmp2 = u2' - x3 ----  
	LDy(u2v)  
	CALL	p256SubInternal<>(SB)  
	RELOAD_PTRS
	MOVV	res+0(FP), b_ptr  
  
	// ---- tmp3 = r * tmp2 ----  
	LDy(rv2)  
	CALL	p256MulInternal<>(SB)  
  
	// ---- y3 = tmp3 - s2'  (diff = y - x, y = tmp3, x = s2') ----  
	LDx(s2v2)
	CALL	p256SubInternal<>(SB)  
	RELOAD_PTRS
	MOVV	res+0(FP), b_ptr  
	STx(y3out)  
  
	MOVV	degflag(0), t0  
	MOVV	t0, ret+24(FP)  
  
	RET
