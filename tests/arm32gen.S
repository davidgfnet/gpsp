
add  r5, r6, r7
adds r3, r9, r10

add   r1,  r2,  r3,  lsl #2
adds  r4,  r5,  r6,  lsr #1
adc   r7,  r8,  r9,  asr #3
adcs  r10, r11, r12, ror #4
sub   r3,  r4,  r5
subs  r6,  r7,  r8,  lsr #5
sbc   r9,  r10, r11, asr #2
sbcs  r12, r1,  r2,  ror #7
and   r5,  r6,  r7,  lsl #1
ands  r8,  r9,  r10, lsr #3
eor   r11, r12, r1,  asr #4
eors  r2,  r3,  r4,  ror #6
orr   r6,  r7,  r8,  lsl #8
orrs  r9,  r10, r11, lsr #2
bic   r12, r2,  r3,  asr #1
bics  r4,  r5,  r6,  ror #5
rsb   r1,  r2,  r3,  lsl #1
rsbs  r4,  r5,  r6,  lsr #2
rsc   r7,  r8,  r9,  asr #3
rscs  r10, r11, r12, ror #4

add   r1,  r2,  r3,  lsl r4
adds  r5,  r6,  r7,  lsr r8
adc   r9,  r10, r11, asr r12
adcs  r2,  r3,  r4,  ror r5
sub   r6,  r7,  r8,  lsl r9
subs  r10, r11, r12, lsr r1
sbc   r3,  r4,  r5,  asr r6
sbcs  r7,  r8,  r9,  ror r10
and   r11, r12, r1,  lsl r2
ands  r3,  r4,  r5,  lsr r6
eor   r7,  r8,  r9,  asr r10
eors  r11, r12, r1,  ror r2
orr   r3,  r4,  r5,  lsl r6
orrs  r7,  r8,  r9,  lsr r10
bic   r11, r12, r1,  asr r2
bics  r3,  r4,  r5,  ror r6
rsb   r7,  r8,  r9,  lsl r10
rsbs  r11, r12, r1,  lsr r2
rsc   r3,  r4,  r5,  asr r6
rscs  r7,  r8,  r9,  ror r10

add   r1,  r2,  #0x12
adds  r3,  r4,  #0x85000000
adc   r5,  r6,  #0x60000005
adcs  r7,  r8,  #0x07900000
sub   r9,  r10, #0x9A
subs  r11, r12, #0x00BD0000
sbc   r2,  r3,  #0xE000000D
sbcs  r4,  r5,  #0x0000F100
and   r6,  r7,  #0x11
ands  r8,  r9,  #0x22000000
eor   r10, r11, #0x30000003
eors  r12, r1,  #0x0EE00000
orr   r2,  r3,  #0x55
orrs  r4,  r5,  #0x00660000
bic   r6,  r7,  #0x70000007
bics  r8,  r9,  #0x00008900
rsb   r10, r11, #0x99
rsbs  r12, r1,  #0xAA000000
rsc   r2,  r3,  #0xB000000B
rscs  r4,  r5,  #0x00CF0000

tst r1, r2
teq r3, r4, lsr #4
cmp r5, r6, asr #8
cmn r7, r8, ror #12

tst r2, r1, lsl r3
teq r4, r3, lsr r5
cmp r6, r5, asr r7
cmn r8, r7, ror r9

tst r1, #0x12
teq r3, #0xAA000000
cmp r5, #0x00560000
cmn r7, #0x00007900

adds r1, r2, r3
adcs r4, r5, r6
subs r7, r8, r9
sbcs r10, r11, r12
ands r1, r3, r5
eors r2, r4, r6
orrs r7, r9, r11
bics r8, r10, r12
rsbs r1, r2, r4
rscs r3, r5, r7

adds r1, r2, #0x12
adcs r3, r4, #0x99000000
subs r5, r6, #0x00560000
sbcs r7, r8, #0x00007900
ands r9, r10, #0x9A
eors r11, r12, #0xBD000000
orrs r1, r3, #0x00DE0000
bics r4, r5, #0x0000F100
rsbs r6, r7, #0x00000081
rscs r8, r9, #0x83000000

mov r1, r2
movs r3, r4, lsr #8
mvn r5, r6, asr #16
mvns r7, r8, ror #24

mov r9, r10, lsl r1
movs r11, r12, lsr r3
mvn r1, r2, asr r5
mvns r3, r4, ror r7

mov r1, #0x00000081
movs r3, #0xC1000000
mvn r5, #0x00F10000
mvns r7, #0x0000E100
mov r9, #0x10000009
movs r11, #0x0A100000
mvn  r1, #0x000B1000
mvns r3, #0x00000D10

