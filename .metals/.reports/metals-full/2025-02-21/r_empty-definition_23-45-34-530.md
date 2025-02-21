error id: _empty_/
file:///D:/Code/VScode/chisel_LA32_cpu_design/src/main/scala/cpu/tool.scala
empty definition using pc, found symbol in pc: _empty_/
semanticdb not found
|empty definition using fallback
non-local guesses:
	 -

Document text:

```scala
import chisel3._
import chisel3.util._

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
    val mem_we            = Output(Bool()) 
    val wb_from_mem       = Output(Bool()) 
    val sign_ext_offs26   = Output(Bool()) 
    val base_pc_add_offs  = Output(Bool()) 
    val base_pc_from_rj   = Output(Bool()) 
    val need_rf_raddr1    = Output(Bool())
    val need_rf_raddr2    = Output(Bool())
    val inst_cancel       = Output(Bool())
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
  val inst_pcaddu12i = op_31_26_d(0b00_0111) & (!io.op(10))
  val inst_and    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1001)
  val inst_or     = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1010)
  val inst_xor    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1011)
  val inst_andi   = op_31_26_d(0b00_0000) & op_25_22_d(0b1101)
  val inst_ori    = op_31_26_d(0b00_0000) & op_25_22_d(0b1110)
  val inst_xori   = op_31_26_d(0b00_0000) & op_25_22_d(0b1111)

  val inst_mul_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b1_1000)
  val inst_mulh_w = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b1_1001)
  val inst_mulh_wu= op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b1_1010)

  val inst_addi_w = op_31_26_d(0b00_0000) & op_25_22_d(0b1010)
  val inst_lu12i_w= op_31_26_d(0b00_0101) & (!io.op(10))
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

  val inst_ld_w = op_31_26_d(0b00_1010) & op_25_22_d(0b0010)
  val inst_st_w = op_31_26_d(0b00_1010) & op_25_22_d(0b0110)
  // 控制信号生成(新指令需要判断rf1和rf2的读取情况)
  io.cs.src_reg_is_rd := inst_beq | inst_bne | inst_st_w
  io.cs.w_addr_is_1 := inst_bl
  // io.cs.rf_we := !(inst_b | inst_beq | inst_bne | inst_st_w)
  io.cs.rf_we:=inst_add_w|inst_sub_w |inst_slt |inst_sltu |inst_nor |inst_and |inst_or |inst_xor |
               inst_addi_w|inst_pcaddu12i |inst_lu12i_w |inst_slli_w |inst_srli_w |inst_srai_w |inst_sll_w|inst_srl_w|inst_sra_w|
               inst_jirl |inst_bl |inst_ld_w |inst_slti|inst_sltui|inst_andi|inst_ori|inst_xori|
               inst_mul_w|inst_mulh_w|inst_mulh_wu
  // sel_src2独热码生成
  val src2_is_R_data2 = inst_add_w|inst_sub_w|inst_slt|inst_sltu|inst_nor|inst_and|inst_or|inst_xor|inst_sll_w|inst_srl_w|inst_sra_w|inst_mul_w|inst_mulh_w|inst_mulh_wu
  val src2_is_ui12 = inst_andi|inst_ori|inst_xori
  val src2_is_si12 = inst_addi_w|inst_ld_w|inst_st_w|inst_slli_w|inst_srli_w|inst_srai_w|inst_slti|inst_sltui
  val src2_is_si20 = inst_lu12i_w|inst_pcaddu12i
  val src2_is_4 = inst_jirl|inst_bl
  io.cs.sel_src2 := Cat(src2_is_R_data2,src2_is_ui12,src2_is_si12,src2_is_si20,src2_is_4)
  io.cs.src1_is_pc := inst_jirl|inst_bl|inst_pcaddu12i
  // ALU_OP独热码生成
  val alu_add = inst_add_w|inst_addi_w|inst_jirl|inst_bl|inst_pcaddu12i
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
  io.cs.mem_we := inst_st_w
  io.cs.wb_from_mem := inst_ld_w
  io.cs.sign_ext_offs26 := inst_b|inst_bl
  io.cs.base_pc_add_offs := inst_jirl|inst_b|inst_bl|(inst_beq&&io.rj_eq_rd)|(inst_bne&&(!io.rj_eq_rd))
  io.cs.base_pc_from_rj := inst_jirl
  
  io.cs.need_rf_raddr1:=inst_add_w|inst_sub_w|inst_addi_w|inst_slt|inst_sltu|inst_and|inst_or|inst_nor|inst_xor|
                        inst_slli_w|inst_srli_w|inst_srai_w|inst_beq|inst_bne|inst_jirl|inst_st_w|inst_ld_w|
                        inst_slti|inst_sltui|inst_andi|inst_ori|inst_xori|inst_sll_w|inst_srl_w|inst_sra_w|
                        inst_mul_w|inst_mulh_w|inst_mulh_wu

  io.cs.need_rf_raddr2:=inst_add_w|inst_sub_w|inst_slt|inst_sltu|inst_and|inst_or|inst_nor|inst_xor|
                        inst_beq|inst_bne|inst_st_w|inst_sll_w|inst_srl_w|inst_sra_w|
                        inst_mul_w|inst_mulh_w|inst_mulh_wu

  io.cs.inst_cancel:=inst_jirl|inst_b|inst_bl|(inst_beq&&io.rj_eq_rd)|(inst_bne&&(!io.rj_eq_rd))

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
```

#### Short summary: 

empty definition using pc, found symbol in pc: _empty_/