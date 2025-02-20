cpu实现的指令集合
=======================
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
 b               offs26
 bl              offs26
 jirl    rd, rj, offs16
```
### 普通访存指令
```
 ld.w rd, rj, si12
 st.w rd, rj, si12
```