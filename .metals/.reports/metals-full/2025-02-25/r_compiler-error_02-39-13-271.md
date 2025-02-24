file:///D:/Code/VScode/chisel_LA32_cpu_design/src/main/scala/cpu/tool.scala
### java.lang.IndexOutOfBoundsException: -1

occurred in the presentation compiler.

presentation compiler configuration:


action parameters:
offset: 24289
uri: file:///D:/Code/VScode/chisel_LA32_cpu_design/src/main/scala/cpu/tool.scala
text:
```scala
import chisel3._
import chisel3.util._
import chisel3.experimental._
class N_2N_Decoder(n: Int) extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(n.W))
    val out = Output(UInt((1 << n).W))
  })

  io.out := 1.U << io.in
}
class Inst_Frag_Decoder extends Module {
  class controlBundle extends Bundle {
    val src_reg_is_rd     = Output(Bool())        
    val w_addr_is_1       = Output(Bool())      
    val rf_we             = Output(Bool()) 
    val sel_src2          = Output(UInt(4.W))    
    val src1_is_pc        = Output(Bool())      
    val alu_op            = Output(UInt(12.W)) 
    val mem_we            = Output(Bool()) 
    val wb_from_mem       = Output(Bool()) 
    val sign_ext_offs26   = Output(Bool()) 
    val base_pc_add_offs  = Output(Bool()) 
    val base_pc_from_rj   = Output(Bool()) 
}
  val io = IO(new Bundle {
    val op = Input(UInt(17.W))
    val rj_eq_rd = Input(Bool())
    val cs = new controlBundle
  })
  val Decoder6_64 = Module(new N_2N_Decoder(6))
  val Decoder5_32 = Module(new N_2N_Decoder(5))
  val Decoder4_16 = Module(new N_2N_Decoder(4))
  val Decoder2_4 = Module(new N_2N_Decoder(2))
  Decoder6_64.io.in := io.op(16, 11)
  Decoder4_16.io.in := io.op(10, 7)
  Decoder2_4.io.in := io.op(6, 5)
  Decoder5_32.io.in := io.op(4, 0)
  val op_31_26_d = Decoder6_64.io.out
  val op_25_22_d = Decoder4_16.io.out
  val op_21_20_d = Decoder2_4.io.out
  val op_19_15_d = Decoder5_32.io.out
  // 指令判断
  val inst_add_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_0000)
  val inst_sub_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_0010)
  val inst_slt    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_0100)
  val inst_sltu   = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_0101)
  val inst_nor    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1000)
  val inst_and    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1001)
  val inst_or     = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1010)
  val inst_xor    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1011)
  val inst_addi_w = op_31_26_d(0b00_0000) & op_25_22_d(0b1010)
  val inst_lu12i_w= op_31_26_d(0b00_0101) & (!io.op(10))

  val inst_slli_w = op_31_26_d(0b00_0000) & op_25_22_d(0b0001) & op_21_20_d(0b00) & op_19_15_d(0b0_0001)
  val inst_srli_w = op_31_26_d(0b00_0000) & op_25_22_d(0b0001) & op_21_20_d(0b00) & op_19_15_d(0b0_1001)
  val inst_srai_w = op_31_26_d(0b00_0000) & op_25_22_d(0b0001) & op_21_20_d(0b00) & op_19_15_d(0b1_0001)

  val inst_jirl = op_31_26_d(0b01_0011)
  val inst_b    = op_31_26_d(0b01_0100)
  val inst_bl   = op_31_26_d(0b01_0101)
  val inst_beq  = op_31_26_d(0b01_0110)
  val inst_bne  = op_31_26_d(0b01_0111)

  val inst_ld_w = op_31_26_d(0b00_1010) & op_25_22_d(0b0010)
  val inst_st_w = op_31_26_d(0b00_1010) & op_25_22_d(0b0110)
  // 控制信号生成
  io.cs.src_reg_is_rd := inst_beq | inst_bne | inst_st_w
  io.cs.w_addr_is_1 := inst_bl
  // io.cs.rf_we := !(inst_b | inst_beq | inst_bne | inst_st_w)
  io.cs.rf_we:=inst_add_w|inst_sub_w |inst_slt |inst_sltu |inst_nor |inst_and |inst_or |inst_xor |inst_addi_w |inst_lu12i_w |inst_slli_w |inst_srli_w |inst_srai_w |inst_jirl |inst_bl |inst_ld_w 
  // sel_src2独热码生成
  val src2_is_R_data2 = inst_add_w|inst_sub_w|inst_slt|inst_sltu|inst_nor|inst_and|inst_or|inst_xor
  val src2_is_si12 = inst_addi_w|inst_ld_w|inst_st_w|inst_slli_w|inst_srli_w|inst_srai_w
  val src2_is_si20 = inst_lu12i_w
  val src2_is_4 = inst_jirl|inst_bl
  io.cs.sel_src2 := Cat(src2_is_R_data2,src2_is_si12,src2_is_si20,src2_is_4)
  io.cs.src1_is_pc := inst_jirl|inst_bl
  // ALU_OP独热码生成
  val alu_add = inst_add_w|inst_addi_w|inst_jirl|inst_bl
  io.cs.alu_op := Cat( alu_add,inst_sub_w,inst_slt,inst_sltu,
                    inst_nor,inst_and,inst_or,inst_xor,inst_lu12i_w,
                    inst_slli_w,inst_srli_w,inst_srai_w)
  io.cs.mem_we := inst_st_w
  io.cs.wb_from_mem := inst_ld_w
  io.cs.sign_ext_offs26 := inst_b|inst_bl
  io.cs.base_pc_add_offs := inst_jirl|inst_b|inst_bl|(inst_beq&&io.rj_eq_rd)|(inst_bne&&(!io.rj_eq_rd))
  io.cs.base_pc_from_rj := inst_jirl

}
class Inst_Frag_Decoder_pipline extends Module {
  class controlBundle extends Bundle {
    val src_reg_is_rd     = Output(Bool())        
    val w_addr_is_1       = Output(Bool())      
    val rf_we             = Output(Bool()) 
    val sel_src2          = Output(UInt(5.W))    
    val src1_is_pc        = Output(Bool())      
    val alu_op            = Output(UInt(13.W)) 
    val mul_op            = Output(UInt(2.W))
    val div_op            = Output(UInt(3.W))
    val mem_we            = Output(Bool()) 
    val mem_pattern       = Output(UInt(3.W))
    val wb_from_mem       = Output(Bool()) 
    val sign_ext_offs26   = Output(Bool()) 
    val base_pc_add_offs  = Output(Bool()) 
    val base_pc_from_rj   = Output(Bool()) 
    val need_rf_raddr1    = Output(Bool())
    val need_rf_raddr2    = Output(Bool())
    val inst_cancel       = Output(Bool())
    val instNoExist       = Output(Bool())
}
  val io = IO(new Bundle {
    val op = Input(UInt(32.W))
    val rj_eq_rd = Input(Bool())
    val rj_less_rd = Input(Bool())
    val rj_lessu_rd = Input(Bool())
    val cs = new controlBundle
  })
  val Decoder6_64 = Module(new N_2N_Decoder(6))
  val Decoder5_32 = Module(new N_2N_Decoder(5))
  val Decoder4_16 = Module(new N_2N_Decoder(4))
  val Decoder2_4 = Module(new N_2N_Decoder(2))
  Decoder6_64.io.in := io.op(31,26)
  Decoder4_16.io.in := io.op(25,22)
  Decoder2_4.io.in :=  io.op(21,20)
  Decoder5_32.io.in := io.op(19,15)
  val op_31_26_d = Decoder6_64.io.out
  val op_25_22_d = Decoder4_16.io.out
  val op_21_20_d = Decoder2_4.io.out
  val op_19_15_d = Decoder5_32.io.out
  // 指令判断
  val inst_add_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_0000)
  val inst_sub_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_0010)
  val inst_slt    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_0100)
  val inst_sltu   = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_0101)
  val inst_nor    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1000)
  val inst_pcaddu12i = op_31_26_d(0b00_0111) & (!io.op(25))
  val inst_and    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1001)
  val inst_or     = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1010)
  val inst_xor    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1011)
  val inst_andi   = op_31_26_d(0b00_0000) & op_25_22_d(0b1101)
  val inst_ori    = op_31_26_d(0b00_0000) & op_25_22_d(0b1110)
  val inst_xori   = op_31_26_d(0b00_0000) & op_25_22_d(0b1111)

  val inst_mul_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b1_1000)
  val inst_mulh_w = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b1_1001)
  val inst_mulh_wu= op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b1_1010)
  
  val inst_div_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b10) & op_19_15_d(0b0_000)
  val inst_mod_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b10) & op_19_15_d(0b0_0001)
  val inst_div_wu = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b10) & op_19_15_d(0b0_0010)
  val inst_mod_wu = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b10) & op_19_15_d(0b0_0011)

  val inst_addi_w = op_31_26_d(0b00_0000) & op_25_22_d(0b1010)
  val inst_lu12i_w= op_31_26_d(0b00_0101) & (!io.op(25))
  val inst_slti   = op_31_26_d(0b00_0000) & op_25_22_d(0b1000)
  val inst_sltui  = op_31_26_d(0b00_0000) & op_25_22_d(0b1001)

  val inst_sll_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1110)
  val inst_srl_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1111)
  val inst_sra_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b1_0000)

  val inst_slli_w = op_31_26_d(0b00_0000) & op_25_22_d(0b0001) & op_21_20_d(0b00) & op_19_15_d(0b0_0001)
  val inst_srli_w = op_31_26_d(0b00_0000) & op_25_22_d(0b0001) & op_21_20_d(0b00) & op_19_15_d(0b0_1001)
  val inst_srai_w = op_31_26_d(0b00_0000) & op_25_22_d(0b0001) & op_21_20_d(0b00) & op_19_15_d(0b1_0001)

  val inst_jirl = op_31_26_d(0b01_0011)
  val inst_b    = op_31_26_d(0b01_0100)
  val inst_bl   = op_31_26_d(0b01_0101)
  val inst_beq  = op_31_26_d(0b01_0110)
  val inst_bne  = op_31_26_d(0b01_0111)
  val inst_blt  = op_31_26_d(0b01_1000)
  val inst_bge  = op_31_26_d(0b01_1001)
  val inst_bltu = op_31_26_d(0b01_1010)
  val inst_bgeu = op_31_26_d(0b01_1011)

  val inst_ld_b = op_31_26_d(0b00_1010) & op_25_22_d(0b0000)
  val inst_ld_h = op_31_26_d(0b00_1010) & op_25_22_d(0b0001)
  val inst_ld_w = op_31_26_d(0b00_1010) & op_25_22_d(0b0010)
  val inst_ld_bu= op_31_26_d(0b00_1010) & op_25_22_d(0b1000)
  val inst_ld_hu= op_31_26_d(0b00_1010) & op_25_22_d(0b1001)

  val inst_st_b = op_31_26_d(0b00_1010) & op_25_22_d(0b0100)
  val inst_st_h = op_31_26_d(0b00_1010) & op_25_22_d(0b0101)
  val inst_st_w = op_31_26_d(0b00_1010) & op_25_22_d(0b0110)

  val rj0=(io.op(9,5)===0.U(5.W))
  val rj1=(io.op(9,5)===1.U(5.W))
  val inst_csrrd  = op_31_26_d(0b00_0001)&(!io.op(25))&(!io.op(25))&rj0
  val inst_csrwr  = op_31_26_d(0b00_0001)&(!io.op(25))&(!io.op(25))&rj1
  val inst_csrxchg= op_31_26_d(0b00_0001)&(!io.op(25))&(!io.op(25))&(!rj0)&(!rj1)

  val inst_ertn    = op_31_26_d(0b00_0001) & op_25_22_d(0b1001) & op_21_20_d(0b00) & op_19_15_d(0b1_0000) &(io.op(14,10)===0b01110.U(5.W))&rj0&(io.op(4,0)===0.U(5.W))
  val inst_syscall = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b10) & op_19_15_d(0b1_0110)
  //指令不存在异常
  io.cs.instNoExist := !(inst_add_w|inst_sub_w|inst_slt|inst_sltu|inst_nor|inst_pcaddu12i|inst_and|inst_or|inst_xor|inst_andi|inst_ori|inst_xori| 
                        inst_mul_w|inst_mulh_w|inst_mulh_wu|inst_div_w|inst_mod_w|inst_div_wu|inst_mod_wu|inst_addi_w|inst_lu12i_w|inst_slti|
                        inst_sltui|inst_sll_w|inst_srl_w|inst_sra_w|inst_slli_w|inst_srli_w|inst_srai_w|inst_bne|inst_blt|inst_bge|inst_bltu|
                        inst_bgeu|inst_ld_b|inst_ld_h|inst_ld_w|inst_ld_bu|inst_ld_hu|inst_st_b|inst_st_h|inst_st_w|
                        inst_csrrd|inst_csrwr|inst_csrxchg|inst_ertn|inst_syscall)
  // 控制信号生成(新指令需要判断rf1和rf2的读取情况)
  io.cs.src_reg_is_rd := inst_beq | inst_bne | inst_st_w|inst_blt|inst_bltu|inst_bge|inst_bgeu|
                         inst_st_b| inst_st_h
  io.cs.w_addr_is_1 := inst_bl
  // io.cs.rf_we := !(inst_b | inst_beq | inst_bne | inst_st_w)
  io.cs.rf_we:=inst_add_w|inst_sub_w |inst_slt |inst_sltu |inst_nor |inst_and |inst_or |inst_xor |
               inst_addi_w|inst_pcaddu12i |inst_lu12i_w |inst_slli_w |inst_srli_w |inst_srai_w |inst_sll_w|inst_srl_w|inst_sra_w|
               inst_jirl |inst_bl |inst_ld_w |inst_slti|inst_sltui|inst_andi|inst_ori|inst_xori|
               inst_mul_w|inst_mulh_w|inst_mulh_wu|inst_div_w|inst_div_wu|inst_mod_w|inst_mod_wu|
               inst_ld_b|inst_ld_bu|inst_ld_h|inst_ld_hu
  // sel_src2独热码生成
  val src2_is_R_data2 = inst_add_w|inst_sub_w|inst_slt|inst_sltu|inst_nor|inst_and|inst_or|inst_xor|inst_sll_w|inst_srl_w|inst_sra_w|inst_mul_w|inst_mulh_w|inst_mulh_wu|inst_div_w|inst_div_wu|inst_mod_w|inst_mod_wu
  val src2_is_ui12 = inst_andi|inst_ori|inst_xori
  val src2_is_si12 = inst_addi_w|inst_ld_w|inst_st_w|inst_slli_w|inst_srli_w|inst_srai_w|inst_slti|inst_sltui|
                     inst_ld_b|inst_ld_bu|inst_ld_h|inst_ld_hu|inst_st_b| inst_st_h
  val src2_is_si20 = inst_lu12i_w|inst_pcaddu12i
  val src2_is_4 = inst_jirl|inst_bl
  io.cs.sel_src2 := Cat(src2_is_R_data2,src2_is_ui12,src2_is_si12,src2_is_si20,src2_is_4)
  io.cs.src1_is_pc := inst_jirl|inst_bl|inst_pcaddu12i
  // 除法和mod指令的div_op
  val need_divmodule = inst_div_w|inst_div_wu|inst_mod_w|inst_mod_wu
  val div_or_mod = (inst_div_w|inst_div_wu)&&(~(inst_mod_w|inst_mod_wu))
  val div_sign_unsign = (inst_div_w|inst_mod_w)&&(~(inst_div_wu|inst_mod_wu))
  io.cs.div_op := Cat(need_divmodule,div_or_mod,div_sign_unsign)
  // ALU_OP独热码生成
  val alu_add = inst_add_w|inst_addi_w|inst_jirl|inst_bl|inst_pcaddu12i|inst_ld_b|inst_ld_bu|inst_ld_h|inst_ld_hu|inst_st_b| inst_st_h
  val alu_mul = inst_mul_w|inst_mulh_w|inst_mulh_wu
  val mul_h   = inst_mulh_w|inst_mulh_wu
  val mul_sign = inst_mulh_w
  val sign_less = inst_slt|inst_slti
  val unsign_less = inst_sltu |inst_sltui
  val alu_op_and  = inst_and  |inst_andi
  val alu_op_or   = inst_or   |inst_ori
  val alu_op_xor  = inst_xor  |inst_xori
  val alu_op_sll  =inst_slli_w|inst_sll_w
  val alu_op_srl  =inst_srli_w|inst_srl_w
  val alu_op_sra  =inst_srai_w|inst_sra_w
  io.cs.mul_op :=Cat(mul_h,mul_sign)
  io.cs.alu_op := Cat(alu_add,inst_sub_w,sign_less,unsign_less,
                    inst_nor,alu_op_and,alu_op_or,alu_op_xor,inst_lu12i_w,
                    alu_op_sll,alu_op_srl,alu_op_sra,alu_mul)
  val mem_is_w= inst_ld_w|inst_st_w
  val mem_b_h = (inst_ld_b|inst_ld_bu|inst_st_b)&(~(inst_ld_h|inst_ld_hu|inst_st_h))
  val mem_s_u = (inst_ld_b|inst_ld_h)&(~(inst_ld_bu|inst_ld_hu))
  io.cs.mem_we := inst_st_w|inst_st_b|inst_st_h
  io.cs.mem_pattern:= Cat(mem_is_w,mem_b_h,mem_s_u)
  io.cs.wb_from_mem := inst_ld_w|inst_ld_b|inst_ld_bu|inst_ld_h|inst_ld_hu
  io.cs.sign_ext_offs26 := inst_b|inst_bl
  io.cs.base_pc_add_offs := inst_jirl|inst_b|inst_bl|(inst_beq&&io.rj_eq_rd)|(inst_bne&&(!io.rj_eq_rd))|
                            (inst_blt&&io.rj_less_rd)|(inst_bltu&&io.rj_lessu_rd)|
                            (inst_bge&&(~io.rj_less_rd))|(inst_bgeu&&(~io.rj_lessu_rd))
  io.cs.base_pc_from_rj := inst_jirl
  
  io.cs.need_rf_raddr1:=inst_add_w|inst_sub_w|inst_addi_w|inst_slt|inst_sltu|inst_and|inst_or|inst_nor|inst_xor|
                        inst_slli_w|inst_srli_w|inst_srai_w|inst_beq|inst_bne|inst_jirl|inst_st_w|inst_ld_w|
                        inst_slti|inst_sltui|inst_andi|inst_ori|inst_xori|inst_sll_w|inst_srl_w|inst_sra_w|
                        inst_mul_w|inst_mulh_w|inst_mulh_wu|inst_div_w|inst_div_wu|inst_mod_w|inst_mod_wu|
                        inst_blt|inst_bltu|inst_bge|inst_bgeu|
                        inst_ld_b|inst_ld_bu|inst_ld_h|inst_ld_hu|inst_st_b|inst_st_h

  io.cs.need_rf_raddr2:=inst_add_w|inst_sub_w|inst_slt|inst_sltu|inst_and|inst_or|inst_nor|inst_xor|
                        inst_beq|inst_bne|inst_st_w|inst_sll_w|inst_srl_w|inst_sra_w|
                        inst_mul_w|inst_mulh_w|inst_mulh_wu|inst_div_w|inst_div_wu|inst_mod_w|inst_mod_wu|
                        inst_blt|inst_bltu|inst_bge|inst_bgeu|inst_st_b|inst_st_h

  io.cs.inst_cancel:=inst_jirl|inst_b|inst_bl|(inst_beq&&io.rj_eq_rd)|(inst_bne&&(!io.rj_eq_rd))|
                     (inst_blt&&io.rj_less_rd)|(inst_bltu&&io.rj_lessu_rd)|
                     (inst_bge&&(~io.rj_less_rd))|(inst_bgeu&&(~io.rj_lessu_rd))

}
class RegFile extends Module {
  val io = IO(new Bundle {
    val raddr1 = Input(UInt(5.W))
    val raddr2 = Input(UInt(5.W))
    val rdata1 = Output(SInt(32.W))
    val rdata2 = Output(SInt(32.W))

    val we = Input(Bool())
    val waddr = Input(UInt(5.W))
    val wdata = Input(SInt(32.W))
  })
  // 声明和初始化32个32位寄存器
  val reg = RegInit(VecInit(Seq.fill(32)(0.S(32.W))))
  // 阻止对 0号寄存器的写入
  when(io.we && io.waddr =/= 0.U) {
    reg(io.waddr) := io.wdata
  }
  // val rdata1=Mux(io.we &&(io.waddr===io.raddr1),io.wdata,reg(io.raddr1))
  // val rdata2=Mux(io.we &&(io.waddr===io.raddr2),io.wdata,reg(io.raddr2))
  // 读取对应地址的寄存器同时保证
  io.rdata1 := Mux(io.raddr1 === 0.U, 0.S, reg(io.raddr1))
  io.rdata2 := Mux(io.raddr2 === 0.U, 0.S, reg(io.raddr2))
}
class ALU extends Module {
  val io = IO(new Bundle {
    val alu_op = Input(UInt(13.W))
    val mul_op = Input(UInt(2.W))
    val src1 = Input(SInt(32.W))
    val src2 = Input(SInt(32.W))
    val alu_res = Output(SInt(32.W))
    val mem_addr = Output(UInt(32.W))
  })
  val ui5 = io.src2(4, 0).asUInt
  val add_w_res = io.src1 + io.src2
  val sub_w_res = io.src1 - io.src2
  val slt_res = Mux(io.src1 < io.src2, 1.S, 0.S)
  val sltu_res = Mux(io.src1.asUInt < io.src2.asUInt, 1.S, 0.S)
  val nor_res = ~(io.src1 | io.src2)
  val and_res = io.src1 & io.src2
  val or_res = io.src1 | io.src2
  val xor_res = io.src1 ^ io.src2
  val lu12i_w_res = io.src2
  val slli_w = io.src1 << ui5
  val srli_w = (io.src1.asUInt >> ui5).asSInt
  val srai_w = io.src1 >> ui5
  // io.cs.mul_op :=Cat(mul_h,mul_sign)
  val mul_64_sign   = io.src1*io.src2
  val mul_64_unsign = (io.src1.asUInt)*(io.src2.asUInt)
  val mul_64 = Mux(io.mul_op(0),mul_64_sign,mul_64_unsign.asSInt)//mul_sign有无符号乘法
  val mul_res = Mux(io.mul_op(1),mul_64(63,32).asSInt,mul_64(31,0).asSInt)//mul_h乘法高部还是低部
  io.mem_addr := add_w_res.asUInt
  io.alu_res := Mux1H(
    io.alu_op,
    Seq(
      mul_res,
      srai_w,
      srli_w,
      slli_w,
      lu12i_w_res,
      xor_res,
      or_res,
      and_res,
      nor_res,
      sltu_res,
      slt_res,
      sub_w_res,
      add_w_res
    )
  )
}
class div_sign extends BlackBox {
  val io = IO(new Bundle {
    val aclk = Input(Clock())
    val s_axis_divisor_tdata=Input(SInt(32.W))//除数
    val s_axis_dividend_tdata=Input(SInt(32.W))//被除数
    val s_axis_divisor_tvalid=Input(Bool())
    val s_axis_dividend_tvalid=Input(Bool())
    val s_axis_divisor_tready=Output(Bool())
    val s_axis_dividend_tready=Output(Bool())
    val m_axis_dout_tdata=Output(UInt(64.W))
    val m_axis_dout_tvalid=Output(Bool())
  })
  //使用xilinx的div IP实现
}
class div_unsign extends BlackBox {
  val io = IO(new Bundle {
    val aclk = Input(Clock())
    val s_axis_divisor_tdata=Input(UInt(32.W))//除数
    val s_axis_dividend_tdata=Input(UInt(32.W))//被除数
    val s_axis_divisor_tvalid=Input(Bool())
    val s_axis_dividend_tvalid=Input(Bool())
    val s_axis_divisor_tready=Output(Bool())
    val s_axis_dividend_tready=Output(Bool())
    val m_axis_dout_tdata=Output(UInt(64.W))
    val m_axis_dout_tvalid=Output(Bool())
  })
  //使用xilinx的div IP实现
}
class Block_Judge extends Module{
  val io = IO(new Bundle {
    val need_rf_raddr1 = Input(Bool())
    val need_rf_raddr2 = Input(Bool())
    val rf_raddr1 = Input(UInt(5.W))
    val rf_rdata1 = Input(SInt(32.W))
    val rf_raddr2 = Input(UInt(5.W))
    val rf_rdata2 = Input(SInt(32.W))
    val exe_wb_from_mem = Input(Bool())
    val exe_rf_we = Input(Bool())
    val exe_rf_waddr = Input(UInt(5.W))
    val exe_alu_res = Input(SInt(32.W))
    val mem_rf_we = Input(Bool())
    val mem_rf_waddr = Input(UInt(5.W))
    val mem_wb_data = Input(SInt(32.W))
    val wb_rf_we = Input(Bool())
    val wb_rf_waddr = Input(UInt(5.W))
    val wb_wb_data = Input(SInt(32.W))
    val forward_rf_rdata1 =Output(SInt(32.W))
    val forward_rf_rdata2 =Output(SInt(32.W))
    val needBlock = Output(Bool())
  })
  val block_rf1 = Wire(Bool())
  val block_rf2 = Wire(Bool())
  when(io.need_rf_raddr1){
    when(io.rf_raddr1=/=0.U){
      when(io.exe_rf_we&&(io.rf_raddr1===io.exe_rf_waddr)){
           when(io.exe_wb_from_mem){
            block_rf1:=true.B
            io.forward_rf_rdata1:=io.rf_rdata1
           }.otherwise{
            block_rf1:=false.B
            io.forward_rf_rdata1:=io.exe_alu_res
           }
      }.elsewhen(io.mem_rf_we&&(io.rf_raddr1===io.mem_rf_waddr)){
        block_rf1:=false.B
        io.forward_rf_rdata1:=io.mem_wb_data
      }.elsewhen(io.wb_rf_we&&(io.rf_raddr1===io.wb_rf_waddr)){
        block_rf1:=false.B
        io.forward_rf_rdata1:=io.wb_wb_data
      }.otherwise{
        io.forward_rf_rdata1:=io.rf_rdata1
        block_rf1:=false.B}
    }.otherwise{
      io.forward_rf_rdata1:=io.rf_rdata1
      block_rf1:=false.B}
  }.otherwise{
    io.forward_rf_rdata1:=io.rf_rdata1
    block_rf1:=false.B}

  when(io.need_rf_raddr2){
    when(io.rf_raddr2=/=0.U){
      when(io.exe_rf_we&&(io.rf_raddr2===io.exe_rf_waddr)){
           when(io.exe_wb_from_mem){
            block_rf2:=true.B
            io.forward_rf_rdata2:=io.rf_rdata2
           }.otherwise{
            block_rf2:=false.B
            io.forward_rf_rdata2:=io.exe_alu_res
           }
      }.elsewhen(io.mem_rf_we&&(io.rf_raddr2===io.mem_rf_waddr)){
        block_rf2:=false.B
        io.forward_rf_rdata2:=io.mem_wb_data
      }.elsewhen(io.wb_rf_we&&(io.rf_raddr2===io.wb_rf_waddr)){
        block_rf2:=false.B
        io.forward_rf_rdata2:=io.wb_wb_data
      }.otherwise{
        io.forward_rf_rdata2:=io.rf_rdata2
        block_rf2:=false.B}
    }.otherwise{
      io.forward_rf_rdata2:=io.rf_rdata2
      block_rf2:=false.B}
  }.otherwise{
    io.forward_rf_rdata2:=io.rf_rdata2
    block_rf2:=false.B}
  io.needBlock:=block_rf1||block_rf2
}
class CSR extends Module{
  val io = IO(new Bundle {
    val csr_re = Input(Bool())
    val csr_num = Input(UInt(14.W))
    val csr_rvalue = Output(UInt(32.W))
    val csr_we = Input(Bool())
    val csr_wmask = Input(UInt(32.W))
    val csr_wvalue = Input(UInt(32.W))
    val csr_ex_entry = Output(UInt(32.W))//异常处理入口地址
    val csr_has_int = Output(Bool())//中断有效信号
    val csr_ertn_flush = Input(Bool())//ERTN指令
    val csr_wb_ex = Input(Bool())//触发异常处理
    val csr_wb_ecode = Input(UInt(6.W))//例外类型一级编码
    val csr_wb_esubcode = Input(UInt(9.W))//例外类型二级编码
  })
  //寄存器地址声明
  val CRMD_ADDR   = 0X0.U(14.W)
  val PRMD_ADDR   = 0X1.U(14.W)
  val ECFG_ADDR   = 0X4.U(14.W)
  val ESTAT_ADDR  = 0X5.U(14.W)
  val ERA_ADDR    = 0X6.U(14.W)
  val EENTRY_ADDR = 0XC.U(14.W)
  val SAVE0_ADDR  = 0X30.U(14.W)
  val SAVE1_ADDR  = 0X31.U(14.W)
  val SAVE2_ADDR  = 0X32.U(14.W)
  val SAVE3_ADDR  = 0X33.U(14.W)
  val TCFG_ADDR   = 0x41.U(14.W)
  val TICLR_ADDR  = 0X44.U(14.W)
  //寄存器声明和初始化
  //CRMD
  val csr_crmd_plv = RegInit(0.U(2.W))
  val csr_crmd_ie  = RegInit(0.U(1.W))
  val csr_crmd_da  = RegInit(0.U(1.W))
  val csr_crmd_pg  = RegInit(0.U(1.W))
  val csr_crmd_datf= RegInit(0.U(2.W))
  val csr_crmd_datm= RegInit(0.U(2.W))
  //PRMD
  val csr_prmd_pplv = RegInit(0.U(2.W))
  val csr_prmd_pie  = RegInit(0.U(1.W))
  //ECFG
  val csr_ecfg_lie = RegInit(0.U(13.W))
  //ESTAT
  val csr_estat_is = RegInit(0.U(13.W))
  //TCFG
  val csr_tcfg_en  = RegInit(0.U(1.W))
  //TICLR
  val csr_ticlr_clr = RegInit(0.U(1.W))
  //////////////////////////////
  //CRMD(当前模式信息) 状态寄存器//
  /////////////////////////////
  //PLV域
  when(io.csr_wb_ex){//触发例外置0
    csr_crmd_plv:=0.U(2.W)
  }.elsewhen(io.csr_ertn_flush){//ertn指令
    csr_crmd_plv:=csr_prmd_pplv//将 CSR.PRMD 的 PPLV 域的值恢复到这里
  }.elsewhen(io.csr_we&&(io.csr_num===CRMD_ADDR)){//csr指令写入
    csr_crmd_plv:= (io.csr_wmask(1,0)&io.csr_wvalue(1,0))|
                   (~io.csr_wmask(1,0)&csr_crmd_plv)
  }
  //IE域
  when(io.csr_wb_ex){
    csr_crmd_ie:=0.U(1.W)
  }.elsewhen(io.csr_ertn_flush){
    csr_crmd_ie:=csr_prmd_pie//件将 CSR.PRMD 的 PIE 域的值恢复到这里
  }.elsewhen(io.csr_we&&(io.csr_num===CRMD_ADDR)){//csr指令写入
    csr_crmd_ie:= (io.csr_wmask(2)&io.csr_wvalue(2))|
                  (~io.csr_wmask(2)&csr_crmd_ie)
  }
  //da, pg, datf, datm域
  //当前未实现全部为0

  //////////////////////////////
  //PRMD(例外前模式信息)状态寄存器/
  /////////////////////////////
  //PPLV域
  when(io.csr_wb_ex){//触发例外
    csr_prmd_pplv:=csr_crmd_plv //将 CSR.CRMD 中 PLV 域的旧值记录在这个域。
  }.elsewhen(io.csr_we&&(io.csr_num===PRMD_ADDR)){//csr指令写入
    csr_prmd_pplv:= (io.csr_wmask(1,0)&io.csr_wvalue(1,0))|
                    (~io.csr_wmask(1,0)&csr_prmd_pplv)
  }
  //PIE域
  when(io.csr_wb_ex){
    csr_prmd_pie:=csr_crmd_ie
  }.elsewhen(io.csr_we&&(io.csr_num===PRMD_ADDR)){
    csr_prmd_pie:= (io.csr_wmask(2)&io.csr_wvalue(2))|
                  (~io.csr_wmask(2)&csr_prmd_pie)
  }

  //////////////////////////
  //ECFG(例外控制)状态寄存器///
  //////////////////////////
  //LIE域
  when(io.csr_we&&(io.csr_num===ECFG_ADDR)){
    csr_ecfg_lie:=(io.csr_wmask(12,0)&0x1bff.U&io.csr_wvalue(12,0))|
                  (~io.csr_wmask(12,0)&0x1bff.U&csr_ecfg_lie)
  }
  //////////////////////////
  //ESTAT(例外控制)状态寄存器///
  //////////////////////////
  //IS域
  when(io.csr_we&&(io.csr_num===ESTAT_ADDR)){
    csr_estat_is()@@:=(io.csr_wmask(12,0)&0x1bff.U&io.csr_wvalue(12,0))|
                  (~io.csr_wmask(12,0)&0x1bff.U&csr_ecfg_lie)
  }
  // // 寄存器定义（全部初始化为0）
  // val CRMD   = RegInit(0.U(32.W))  // 0x0
  // val PRMD   = RegInit(0.U(32.W))  // 0x1
  // val ESTAT  = RegInit(0.U(32.W))  // 0x5
  // val ERA    = RegInit(0.U(32.W))  // 0x6
  // val EENTRY = RegInit(0.U(32.W))  // 0xc
  // val SAVE0  = RegInit(0.U(32.W))  // 0x30
  // val SAVE1  = RegInit(0.U(32.W))  // 0x31
  // val SAVE2  = RegInit(0.U(32.W))  // 0x32
  // val SAVE3  = RegInit(0.U(32.W))  // 0x33

  // // 读逻辑
  // io.csr_rvalue := 0.U
  // when(io.csr_re) {
  //   switch(io.csr_num) {
  //     is(0x0.U)  { io.csr_rvalue := CRMD }
  //     is(0x1.U)  { io.csr_rvalue := PRMD }
  //     is(0x5.U)  { io.csr_rvalue := ESTAT }
  //     is(0x6.U)  { io.csr_rvalue := ERA }
  //     is(0xc.U)  { io.csr_rvalue := EENTRY }
  //     is(0x30.U) { io.csr_rvalue := SAVE0 }
  //     is(0x31.U) { io.csr_rvalue := SAVE1 }
  //     is(0x32.U) { io.csr_rvalue := SAVE2 }
  //     is(0x33.U) { io.csr_rvalue := SAVE3 }
  //   }
  // }
  // // 写逻辑（带掩码功能）
  // when(io.csr_we) {
  //   switch(io.csr_num) {
  //     is(0x0.U)  { CRMD   := (CRMD   & (~io.csr_wmask)) | (io.csr_wvalue & io.csr_wmask) }
  //     is(0x1.U)  { PRMD   := (PRMD   & (~io.csr_wmask)) | (io.csr_wvalue & io.csr_wmask) }
  //     is(0x5.U)  { ESTAT  := (ESTAT  & (~io.csr_wmask)) | (io.csr_wvalue & io.csr_wmask) }
  //     is(0x6.U)  { ERA    := (ERA    & (~io.csr_wmask)) | (io.csr_wvalue & io.csr_wmask) }
  //     is(0xc.U)  { EENTRY := (EENTRY & (~io.csr_wmask)) | (io.csr_wvalue & io.csr_wmask) }
  //     is(0x30.U) { SAVE0  := (SAVE0  & (~io.csr_wmask)) | (io.csr_wvalue & io.csr_wmask) }
  //     is(0x31.U) { SAVE1  := (SAVE1  & (~io.csr_wmask)) | (io.csr_wvalue & io.csr_wmask) }
  //     is(0x32.U) { SAVE2  := (SAVE2  & (~io.csr_wmask)) | (io.csr_wvalue & io.csr_wmask) }
  //     is(0x33.U) { SAVE3  := (SAVE3  & (~io.csr_wmask)) | (io.csr_wvalue & io.csr_wmask) }
  //   }
  // }
}
```



#### Error stacktrace:

```
scala.collection.LinearSeqOps.apply(LinearSeq.scala:129)
	scala.collection.LinearSeqOps.apply$(LinearSeq.scala:128)
	scala.collection.immutable.List.apply(List.scala:79)
	dotty.tools.dotc.util.Signatures$.applyCallInfo(Signatures.scala:244)
	dotty.tools.dotc.util.Signatures$.computeSignatureHelp(Signatures.scala:101)
	dotty.tools.dotc.util.Signatures$.signatureHelp(Signatures.scala:88)
	dotty.tools.pc.SignatureHelpProvider$.signatureHelp(SignatureHelpProvider.scala:47)
	dotty.tools.pc.ScalaPresentationCompiler.signatureHelp$$anonfun$1(ScalaPresentationCompiler.scala:422)
```
#### Short summary: 

java.lang.IndexOutOfBoundsException: -1