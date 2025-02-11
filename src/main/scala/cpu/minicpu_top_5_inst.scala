import chisel3._
import chisel3.util._
//调用chisel包
class minicpu_top_5inst extends Module {
  val io = IO(new Bundle {
    val inst_sram_we = Output(Bool())
    val inst_sram_addr = Output(UInt(32.W))
    val inst_sram_wdata = Output(UInt(32.W))
    val inst_sram_rdata = Input(UInt(32.W))

    val data_sram_we = Output(Bool())
    val data_sram_addr = Output(UInt(32.W))
    val data_sram_wdata = Output(SInt(32.W))
    val data_sram_rdata = Input(SInt(32.W))
  })
  val pc = RegInit(UInt(32.W), 0x1bfffffc.U)
  val nextpc = Wire(UInt(32.W))
  pc := nextpc

  io.inst_sram_we := false.B
  io.inst_sram_addr := pc
  io.inst_sram_wdata := 0.U
  val inst = io.inst_sram_rdata

  val op_31_26 = inst(31, 26)
  val op_25_22 = inst(25, 22)
  val op_21_20 = inst(21, 20)
  val op_19_15 = inst(19, 15)
  val rd = inst(4, 0)
  val rj = inst(9, 5)
  val rk = inst(14, 10)
  val i12 = inst(21, 10)
  val offs = inst(25, 10)

  val Decoder6_64 = Module(new N_2N_Decoder(6))
  val Decoder5_32 = Module(new N_2N_Decoder(5))
  val Decoder4_16 = Module(new N_2N_Decoder(4))
  val Decoder2_4 = Module(new N_2N_Decoder(2))
  Decoder6_64.io.in := op_31_26
  Decoder4_16.io.in := op_25_22
  Decoder2_4.io.in := op_21_20
  Decoder5_32.io.in := op_19_15
  val op_31_26_d = Decoder6_64.io.out
  val op_25_22_d = Decoder4_16.io.out
  val op_21_20_d = Decoder2_4.io.out
  val op_19_15_d = Decoder5_32.io.out

  val inst_add_w = op_31_26_d(0) & op_25_22_d(0) & op_21_20_d(1) & op_19_15_d(0)
  val inst_addi_w = op_31_26_d(0) & op_25_22_d(10)
  val inst_ld_w = op_31_26_d(10) & op_25_22_d(2)
  val inst_st_w = op_31_26_d(10) & op_25_22_d(6)
  val inst_bne = op_31_26_d(23)

  val src2_is_imm = inst_st_w | inst_ld_w | inst_addi_w
  val res_from_mem = inst_ld_w
  val gr_we = inst_add_w | inst_ld_w | inst_addi_w
  val mem_we = inst_st_w
  val src_reg_is_rd = inst_bne | inst_st_w

  val rf_raddr1 = rj
  val rf_raddr2 = Mux(src_reg_is_rd, rd, rk)
  val rf_rdata1_rj = Wire(SInt(32.W))
  val rf_rdata2_rdk = Wire(SInt(32.W))
  val rf_wdata = Wire(SInt(32.W))
  val rf_regfile = Module(new RegFile())
  rf_regfile.io.raddr1 := rf_raddr1
  rf_regfile.io.raddr2 := rf_raddr2
  rf_rdata1_rj := rf_regfile.io.rdata1
  rf_rdata2_rdk := rf_regfile.io.rdata2
  rf_regfile.io.we := gr_we
  rf_regfile.io.waddr := rd
  rf_regfile.io.wdata := rf_wdata

  val imm = i12.asSInt
  val src1 = rf_rdata1_rj
  val src2 = Mux(src2_is_imm, imm, rf_rdata2_rdk)
  val add_result = src1 + src2
  rf_wdata := Mux(res_from_mem, io.data_sram_rdata, add_result)
  io.data_sram_we := mem_we
  io.data_sram_addr := add_result.asUInt
  io.data_sram_wdata := rf_rdata2_rdk

  val br_offs = Cat(offs, 0.U(2.W)).asUInt
  val pc_bne_target = pc + br_offs
  val rj_eq_rdk = (rf_rdata1_rj === rf_rdata2_rdk)
  val br_bne_taken = (inst_bne && (!rj_eq_rdk))
  nextpc := Mux(br_bne_taken, pc_bne_target, pc + 4.U)

}
