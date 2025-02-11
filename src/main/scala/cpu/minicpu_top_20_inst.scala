import chisel3._
import chisel3.util._
//调用chisel包
class minicpu_top_20inst extends Module {
  val io = IO(new Bundle {
    val inst_sram_we = Output(Bool())
    val inst_sram_addr = Output(UInt(32.W))
    val inst_sram_wdata = Output(UInt(32.W))
    val inst_sram_rdata = Input(UInt(32.W))

    val data_sram_we = Output(Bool())
    val data_sram_addr = Output(UInt(32.W))
    val data_sram_wdata = Output(SInt(32.W))
    val data_sram_rdata = Input(SInt(32.W))

    val debug_wb_pc = Output(UInt(32.W))
    val debug_wb_rf_we = Output(UInt(4.W))
    val debug_wb_rf_wnum = Output(UInt(5.W))
    val debug_wb_rf_wdata = Output(SInt(32.W))
  })
  // pc更新
  val pc = RegInit(UInt(32.W), 0x1c000000.U)
  val nextpc = Wire(UInt(32.W))
  pc := nextpc
  // inst_sram 信号连线
  io.inst_sram_we := false.B
  io.inst_sram_addr := pc
  io.inst_sram_wdata := 0.U
  // 从inst_sram取指令
  val inst = io.inst_sram_rdata
  // 指令字段提取
  //   val op_31_26 = inst(31, 26)
  //   val op_25_22 = inst(25, 22)
  //   val op_21_20 = inst(21, 20)
  //   val op_19_15 = inst(19, 15)
  val inst_op = inst(31, 15)
  val rj = inst(9, 5)
  val rk = inst(14, 10)
  val rd = inst(4, 0)
  val si12 = inst(21, 10)
  val si20 = inst(24, 5)
  val offs16 = inst(25, 10)
  val offs26 = Cat(inst(9, 0), inst(25, 10))
  // 译码
  val rj_eq_rd = Wire(Bool())
  val inst_frag_decoder = Module(new Inst_Frag_Decoder())
  inst_frag_decoder.io.op := inst_op
  inst_frag_decoder.io.rj_eq_rd := rj_eq_rd
  // 控制信号
  val src_reg_is_rd = inst_frag_decoder.io.cs.src_reg_is_rd
  val w_addr_is_1 = inst_frag_decoder.io.cs.w_addr_is_1
  val rf_we = inst_frag_decoder.io.cs.rf_we
  val sel_src2 = inst_frag_decoder.io.cs.sel_src2
  val src1_is_pc = inst_frag_decoder.io.cs.src1_is_pc
  val alu_op = inst_frag_decoder.io.cs.alu_op
  val mem_we = inst_frag_decoder.io.cs.mem_we
  val wb_from_mem = inst_frag_decoder.io.cs.wb_from_mem
  val sign_ext_offs26 = inst_frag_decoder.io.cs.sign_ext_offs26
  val base_pc_add_offs = inst_frag_decoder.io.cs.base_pc_add_offs
  val base_pc_from_rj = inst_frag_decoder.io.cs.base_pc_from_rj
  // // 指令类型字段译码
  // val inst_frag_decoder = Module(new Inst_Frag_Decoder())
  // inst_frag_decoder.io.op := inst_op
  // val op_31_26_d = inst_frag_decoder.io.op_31_26_d
  // val op_25_22_d = inst_frag_decoder.io.op_25_22_d
  // val op_21_20_d = inst_frag_decoder.io.op_21_20_d
  // val op_19_15_d = inst_frag_decoder.io.op_19_15_d
  // // 指令判断
  // val inst_add_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_0000)
  // val inst_sub_w  = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_0010)
  // val inst_slt    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_0100)
  // val inst_sltu   = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_0101)
  // val inst_nor    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1000)
  // val inst_and    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1001)
  // val inst_or     = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1010)
  // val inst_xor    = op_31_26_d(0b00_0000) & op_25_22_d(0b0000) & op_21_20_d(0b01) & op_19_15_d(0b0_1011)
  // val inst_addi_w = op_31_26_d(0b00_0000) & op_25_22_d(0b1010)
  // val inst_lu12i_w= op_31_26_d(0b00_0101) & (!inst(25))

  // val inst_slli_w = op_31_26_d(0b00_0000) & op_25_22_d(0b0001) & op_21_20_d(0b00) & op_19_15_d(0b0_0001)
  // val inst_srli_w = op_31_26_d(0b00_0000) & op_25_22_d(0b0001) & op_21_20_d(0b00) & op_19_15_d(0b0_1001)
  // val inst_srai_w = op_31_26_d(0b00_0000) & op_25_22_d(0b0001) & op_21_20_d(0b00) & op_19_15_d(0b1_0001)

  // val inst_jirl = op_31_26_d(0b01_0011)
  // val inst_b    = op_31_26_d(0b01_0100)
  // val inst_bl   = op_31_26_d(0b01_0101)
  // val inst_beq  = op_31_26_d(0b01_0110)
  // val inst_bne  = op_31_26_d(0b01_0111)

  // val inst_ld_w = op_31_26_d(0b00_1010) & op_25_22_d(0b0010)
  // val inst_st_w = op_31_26_d(0b00_1010) & op_25_22_d(0b0110)
  // // 控制信号生成
  // val rj_eq_rd = Wire(Bool())
  // val src_reg_is_rd = inst_beq | inst_bne | inst_st_w
  // val w_addr_is_1 = inst_bl
  // val rf_we = !(inst_b | inst_beq | inst_bne | inst_st_w)
  // // sel_src2独热码生成
  // val src2_is_R_data2 = inst_add_w|inst_sub_w|inst_slt|inst_sltu|inst_nor|inst_and|inst_or|inst_xor
  // val src2_is_si12 = inst_addi_w|inst_ld_w|inst_st_w|inst_slli_w|inst_srli_w|inst_srai_w
  // val src2_is_si20 = inst_lu12i_w
  // val src2_is_4 = inst_jirl|inst_bl
  // val sel_src2 = Cat(src2_is_R_data2,src2_is_si12,src2_is_si20,src2_is_4)
  // val src1_is_pc = inst_jirl|inst_bl
  // // ALU_OP独热码生成
  // val alu_add = inst_add_w|inst_addi_w|inst_jirl|inst_bl
  // val alu_op = Cat( alu_add,inst_sub_w,inst_slt,inst_sltu,
  //                   inst_nor,inst_and,inst_or,inst_xor,inst_lu12i_w,
  //                   inst_slli_w,inst_srli_w,inst_srai_w)
  // val mem_we = inst_st_w
  // val wb_from_mem = inst_ld_w
  // val sign_ext_offs26 = inst_b|inst_bl
  // val base_pc_add_offs = inst_jirl|inst_b|inst_bl|(inst_beq&&rj_eq_rd)|(inst_bne&&(!rj_eq_rd))
  // val base_pc_from_rj = inst_jirl

  // 寄存器堆
  val rf_regfile = Module(new RegFile())
  val wb_data = Wire(SInt(32.W))
  val rf_waddr = Wire(UInt(5.W))
  rf_waddr := Mux(w_addr_is_1, 1.U(5.W), rd)
  rf_regfile.io.raddr1 := rj
  rf_regfile.io.raddr2 := Mux(src_reg_is_rd, rd, rk)
  rf_regfile.io.waddr := rf_waddr
  rf_regfile.io.wdata := wb_data
  rf_regfile.io.we := rf_we
  val gr_rj = rf_regfile.io.rdata1
  val gr_rdk = rf_regfile.io.rdata2
  rj_eq_rd := (gr_rj === gr_rdk)
  // 立即数扩展
  val si20_lu12i = Cat(si20, 0.U(12.W)).asSInt
  val si12_sext = si12.asSInt
  val src1 = Mux(src1_is_pc, pc.asSInt, gr_rj)
  // sel_src2=Cat(src2_is_R_data2,src2_is_si12,src2_is_si20,src2_is_4)
  val src2 = Mux1H(sel_src2, Seq(4.S(32.W), si20_lu12i, si12_sext, gr_rdk))
  // ALU运算
  val alu = Module(new ALU())
  alu.io.alu_op := alu_op
  alu.io.src1 := src1
  alu.io.src2 := src2
  val alu_res = alu.io.alu_res
  val mem_addr = alu.io.mem_addr
  // 访问存储器
  io.data_sram_we := mem_we
  io.data_sram_addr := mem_addr
  io.data_sram_wdata := gr_rdk
  val mem_value = io.data_sram_rdata
  wb_data := Mux(wb_from_mem, mem_value, alu_res)
  // pc跳转
  // offs扩展
  val pc_offs = Mux(
    sign_ext_offs26,
    Cat(offs26, 0.U(2.W)).asSInt,
    Cat(offs16, 0.U(2.W)).asSInt
  )
  val pc_add_src1 = Mux(base_pc_add_offs, pc_offs, 4.S(32.W))
  val pc_add_src2 = Mux(base_pc_from_rj, gr_rj, pc.asSInt)
  nextpc := (pc_add_src1 + pc_add_src2).asUInt
  // debug信号
  io.debug_wb_pc := pc
  io.debug_wb_rf_we := Cat(rf_we, rf_we, rf_we, rf_we)
  io.debug_wb_rf_wnum := rf_waddr
  io.debug_wb_rf_wdata := wb_data
}
