.text

//mov %edx, %ecx
//mov %edi, %eax

mov 0x4(%rdi), %ebx
mov 0x7(%rbx), %ebx
mov 0x10111213(%rdi), %esi
mov %ebx, 0x4(%rdi)
mov %ebx, 0x7(%rbx)
mov %esi, 0x10111213(%rdi)
movzx 0x4(%rdi), %ebx
movzx 0x7(%rbx), %ebx
movzx 0x10111213(%rdi), %esi

mov $0x123, %ebx
mov $0x12366, %edx

movl $0x12345, 0x15(%rsi)
movl $0x3333, 0x151617(%rdi)

//and %ecx, %ebx
//xor %ecx, %ebx
//or %ecx, %ebx

andl 0x12(%rcx), %ebx
xorl 0x12(%rcx), %ebx
orl  0x12(%rcx), %ebx
andl 0x1234(%rcx), %ebx
xorl 0x1234(%rcx), %ebx
orl  0x1234(%rcx), %ebx

andl $0x1213, %ebx
xorl $0x1213, %ebx
orl  $0x1213, %ebx

andl $0x12345, 0xaa(%rbx)
andl $0x12345, 0xaabb(%rbx)

shr %cl, %ebx
sar %cl, %ebx
shl %cl, %ebx
ror %cl, %ebx
shr $2, %ebx
sar $3, %ebx
shl $4, %ebx
ror $5, %ebx

//add %ecx, %ebx
//sub %ecx, %ebx
//adc %ecx, %ebx
//sbb %ecx, %ebx
//cmp %ecx, %ebx
//test %ecx, %ebx

add 0x10(%rdi), %ebx
sub 0x20(%rdi), %ebx
//cmp 0x30(%rdi), %ebx

add $0x1234, %ebx
sub $0x5678, %ebx
adc $0x9abc, %ebx
sbb $0xdef0, %ebx
cmp $0x1111, %ebx
test $0x2222, %ebx

addl $0x12345678, 0x10(%rdi)
subl $0x9abcdef0, 0x80(%rdi)
addl $0x12345678, 0x10101010(%rdi)
subl $0x9abcdef0, 0x20202020(%rdi)

mul %ebx
imul %ebx
idiv %ebx

neg %ebx
not %ebx

setc 0x10(%rdi)
setnc 0x1010(%rdi)
cmovc %ecx, %ebx
cmovnc %ecx, %ebx

bt $3, %ebx
bt $7, %ecx
bt $2, 0x10(%rdi)
bt $5, 0x1010(%rdi)

//call 0x12345678

lea 0x10(%rdi), %ebx
lea 0x10101010(%rdi), %esi

cdq
cmc


