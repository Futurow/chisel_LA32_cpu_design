cpu实现的功能
=======================
# 指令
## 基础整数指令
### 算术运算类指令
```
 add.w   rd, rj, rk
 sub.w   rd, rj, rk
 addi.w  rd, rj, si12
 slt     rd, rj, rk
 sltu    rd, rj, rk
 pcaddu12i   rd, si20
 and     rd, rj, rk
 or      rd, rj, rk
 nor     rd, rj, rk
 xor     rd, rj, rk
 andi    rd, rj, ui12
 ori     rd, rj, ui12
 xori    rd, rj, ui12
 lu12i.w rd, si20
 slti    rd, rj, si12
 sltui   rd, rj, si12
 mul.w   rd, rj, rk
 mulh.w  rd, rj, rk
 mulh.wu rd, rj, rk
 div.w   rd, rj, rk
 mod.w   rd, rj, rk
 div.wu  rd, rj, rk
 mod.wu  rd, rj, rk
```
### 移位运算类指令
```
 sll.w   rd, rj, rk
 srl.w   rd, rj, rk
 sra.w   rd, rj, rk

 slli.w  rd, rj, ui5
 srli.w  rd, rj, ui5
 srai.w  rd, rj, ui5
```
### 转移指令
```
 beq     rj, rd, offs16
 bne     rj, rd, offs16
 blt     rj, rd, offs16
 bge     rj, rd, offs16
 bltu    rj, rd, offs16
 bgeu    rj, rd, offs16
 b               offs26
 bl              offs26
 jirl    rd, rj, offs16
```
### 普通访存指令
```
 ld.w  rd, rj, si12
 ld.b  rd, rj, si12
 ld.h  rd, rj, si12
 ld.bu rd, rj, si12
 ld.hu rd, rj, si12
 st.w  rd, rj, si12
 st.b  rd, rj, si12
 st.h  rd, rj, si12
```
### CSR访问指令
```
csrrd   rd, csr_num
csrwr   rd, csr_num
csrxchg rd, rj, csr_num
```

# 例外和中断
## 例外表
| Ecode | EsubCode | 例外代号 | 例外类型       |
| ----- | -------- | -------- | -------------- |
| 0x0   | 0        | INT      | 中断           |
| 0x8   | 0        | ADEF     | 取指地址错例外 |
| 0x9   | 0        | ALE      | 地址非对齐例外 |
| 0xB   | 0        | SYS      | 系统调用例外   |
| 0xC   | 0        | BRK      | 断点例外       |
| 0xD   | 0        | INE      | 指令不存在例外 |