// import chisel3._
// import chisel3.util._
// class pre_IF extends Module {
//   val io = IO(new Bundle {
//     val offs_ext = Input(SInt(32.W))
//     val gr_rj = Input(SInt(32.W))
//     val pc = Input(UInt(32.W))
//     val base_pc_from_rj = Input(Bool())
//     val nextpc = Output(UInt(32.W))
//   })
//   // val valid = Reg(Bool())
//   // val rst = reset.asBool
//   // valid := rst

//   // val pc_add_src1 = io.offs_ext
//   // val pc_add_src2 = Mux(io.base_pc_from_rj, io.gr_rj, io.pc.asSInt)
//   // val nextpc = (pc_add_src1 + pc_add_src2).asUInt
//   // io.nextpc := Mux(valid && (~rst), 0x1c000000.U, nextpc)
//   val pc_add_src1 = io.offs_ext
//   val pc_add_src2 = Mux(io.base_pc_from_rj, io.gr_rj, io.pc.asSInt)
//   val nextpc = (pc_add_src1 + pc_add_src2).asUInt
//   io.nextpc := nextpc
// }
// class IF_stage extends Module {
//   val io = IO(new Bundle {
//     val pre_valid = Input(Bool())
//     val next_ready = Input(Bool())
//     val valid = Output(Bool())
//     val needBlock  = Input(Bool())
//     val br_taken = Input(Bool())
//     val nextpc = Input(UInt(32.W))
//     val inst_sram_rdata = Input(UInt(32.W))
//     val inst = Output(UInt(32.W))
//     val inst_sram_addr = Output(UInt(32.W))
//     val pc = Output(UInt(32.W))
//     val exception_out = Output(UInt(8.W))//has_ex,ex_ecode,ex_esubcode
//     val csr_pc = Input(UInt(32.W))
//     val csr_pc_taken = Input(Bool())
//   })
//   val valid = RegInit(false.B)
//   val ready= true.B
//   val inst_pc = RegInit(UInt(32.W),0x1bfffffc.U)
//   // val inst_pc = RegInit(0x1c000000.U)
//   when(~io.needBlock){
//       inst_pc:=io.inst_sram_addr 
//       valid:=io.pre_valid
//   }
//   io.valid:=valid&&(~io.needBlock)
//   val branch_target = Mux(io.needBlock,inst_pc,Mux(io.br_taken,io.nextpc,inst_pc + 4.U))
//   io.inst_sram_addr := Mux(io.csr_pc_taken,io.csr_pc,branch_target)
//   io.inst := io.inst_sram_rdata
//   io.pc:=inst_pc
//   //最低两位为0
//   val inst_fetch_addr_err =io.inst_sram_addr(1,0)=/=0.U(2.W)
//   when(inst_fetch_addr_err){//取值地址错例外
//     io.exception_out:=Cat(1.U(1.W),0x8.U(6.W),0.U(1.W))
//   }.otherwise{
//     io.exception_out:=0.U(8.W)
//   }
// }
// class ID_stage extends Module {
//   val io = IO(new Bundle {
//     val pre_valid = Input(Bool())
//     val next_ready = Input(Bool())
//     val ready = Output(Bool())
//     val valid = Output(Bool())
//     val inst = Input(UInt(32.W))
//     val pc_in = Input(UInt(32.W))
//     val forward_rf_rdata1 =Input(SInt(32.W))
//     val forward_rf_rdata2 = Input(SInt(32.W))
//     val rf_we_WB = Input(Bool())
//     val wb_data = Input(SInt(32.W))
//     val wb_addr_in = Input(UInt(5.W))
//     val wb_addr_out = Output(UInt(5.W))
//     val rf_we_ID = Output(Bool())
//     val alu_op = Output(UInt(13.W))
//     val mul_op = Output(UInt(2.W))
//     val div_op = Output(UInt(3.W))
//     val mem_we = Output(Bool())
//     val mem_pattern = Output(UInt(3.W))
//     val wb_from_mem = Output(Bool())
//     val br_taken = Output(Bool())
//     val base_pc_from_rj = Output(Bool())
//     val pc_offs = Output(SInt(32.W))
//     val src1 = Output(SInt(32.W))
//     val src2 = Output(SInt(32.W))
//     val to_forward_rf_data1 = Output(SInt(32.W))
//     val to_forward_rf_data2 = Output(SInt(32.W))
//     val rf_data1 = Output(SInt(32.W))
//     val rf_data2 = Output(SInt(32.W))
//     val pc_out = Output(UInt(32.W))
//     val need_rf_raddr1 = Output(Bool())
//     val need_rf_raddr2 = Output(Bool())
//     val rf_raddr1 = Output(UInt(5.W))
//     val rf_raddr2 = Output(UInt(5.W))
//     val needBlock = Input(Bool())
//     val csr_num_out = Output(UInt(14.W))
//     val wb_csr_out = Output(Bool())
//     val csr_we_out = Output(Bool())
//     val csr_open_wmask_out = Output(Bool())
//     val csr_has_int = Input(Bool())
//     val exception_in = Input(UInt(8.W))//has_ex,ex_ecode,ex_esubcode
//     val exception_out = Output(UInt(8.W))
//     val ertn_flush_out = Output(Bool())
//     val clear = Input(Bool())
//     val cntcontrol_out = Output(UInt(3.W))
//   })
//   io.ready := true.B
//   // io.ready:=true.B
//   val valid = RegInit(false.B)
//   val inst = RegInit(UInt(32.W), 0.U)
//   // val inst = RegInit(UInt(32.W), 0.U)
//   val pc = RegInit(UInt(32.W), 0.U)
//   val inst_cancel = Wire(Bool())
//   val exception = RegInit(UInt(8.W), 0.U)
//   when(io.clear){
//     valid:=false.B
//   }.elsewhen(io.pre_valid&&io.ready){
//     valid := true.B&&(~inst_cancel)
//     pc := io.pc_in
//     inst:=io.inst
//     exception:=io.exception_in
//   }.elsewhen(valid&&io.next_ready&&(~io.needBlock)){
//     valid := false.B
//   }
//   io.valid := valid&&(~io.needBlock)

//   // val inst = RegInit(UInt(32.W), 0.U)
//   // val inst = Reg(UInt(32.W))
//   // val pc = RegInit(UInt(32.W), 0x1c000000.U) // 0x1bfffffc
//   io.pc_out := pc

//   val inst_op = inst
//   val rj = inst(9, 5)
//   val rk = inst(14, 10)
//   val rd = inst(4, 0)
//   val si12 = inst(21, 10)
//   val ui12 = inst(21, 10)
//   val si20 = inst(24, 5)
//   val offs16 = inst(25, 10)
//   val offs26 = Cat(inst(9, 0), inst(25, 10))
//   // 译码
//   val rj_eq_rd = Wire(Bool())
//   val rj_less_rd = Wire(Bool())
//   val rj_lessu_rd = Wire(Bool())
//   val inst_frag_decoder = Module(new Inst_Frag_Decoder_pipline())
//   inst_frag_decoder.io.op := inst_op
//   inst_frag_decoder.io.rj_eq_rd   := rj_eq_rd
//   inst_frag_decoder.io.rj_less_rd := rj_less_rd
//   inst_frag_decoder.io.rj_lessu_rd:= rj_lessu_rd
//   // 控制信号
//   val src_reg_is_rd = inst_frag_decoder.io.cs.src_reg_is_rd //
//   val w_addr_is_1 = inst_frag_decoder.io.cs.w_addr_is_1 //
//   io.rf_we_ID := inst_frag_decoder.io.cs.rf_we 
//   val sel_src2 = inst_frag_decoder.io.cs.sel_src2 //
//   val src1_is_pc = inst_frag_decoder.io.cs.src1_is_pc //
//   io.alu_op := inst_frag_decoder.io.cs.alu_op
//   io.mul_op := inst_frag_decoder.io.cs.mul_op
//   io.div_op := inst_frag_decoder.io.cs.div_op
//   io.mem_we := inst_frag_decoder.io.cs.mem_we&&io.valid
//   io.mem_pattern:=inst_frag_decoder.io.cs.mem_pattern
//   io.wb_from_mem := inst_frag_decoder.io.cs.wb_from_mem
//   val sign_ext_offs26 = inst_frag_decoder.io.cs.sign_ext_offs26 //
//   io.br_taken := inst_frag_decoder.io.cs.base_pc_add_offs&&io.valid
//   io.base_pc_from_rj := inst_frag_decoder.io.cs.base_pc_from_rj
//   io.need_rf_raddr1:=inst_frag_decoder.io.cs.need_rf_raddr1
//   io.need_rf_raddr2:=inst_frag_decoder.io.cs.need_rf_raddr2
//   inst_cancel:=inst_frag_decoder.io.cs.inst_cancel&&io.valid
//   // 寄存器堆
//   val rf_regfile = Module(new RegFile())
//   val rf_waddr = Wire(UInt(5.W))
//   io.rf_raddr1:=rj
//   io.rf_raddr2:=Mux(src_reg_is_rd, rd, rk)
//   rf_waddr := Mux(inst_frag_decoder.io.cs.wb_waddr_is_rj,rj,Mux(w_addr_is_1, 1.U(5.W), rd))
//   io.wb_addr_out := rf_waddr
//   rf_regfile.io.raddr1 := io.rf_raddr1
//   rf_regfile.io.raddr2 := io.rf_raddr2
//   rf_regfile.io.waddr := io.wb_addr_in
//   rf_regfile.io.wdata := io.wb_data
//   rf_regfile.io.we := io.rf_we_WB
//   io.to_forward_rf_data1:=rf_regfile.io.rdata1
//   io.to_forward_rf_data2:=rf_regfile.io.rdata2
//   val gr_rj = io.forward_rf_rdata1
//   val gr_rdk = io.forward_rf_rdata2
//   rj_eq_rd   := (gr_rj === gr_rdk)
//   rj_less_rd := (gr_rj < gr_rdk)
//   rj_lessu_rd:= (gr_rj.asUInt < gr_rdk.asUInt)
//   io.rf_data1 := gr_rj
//   io.rf_data2 := gr_rdk
//   // 立即数扩展
//   val si20_lu12i = Cat(si20, 0.U(12.W)).asSInt
//   val si12_sext = si12.asSInt
//   val ui12_zext = Cat(0.U(20.W),ui12).asSInt
//   io.src1 := Mux(src1_is_pc, pc.asSInt, gr_rj)
//   //io.cs.sel_src2 := Cat(src2_is_R_data2,src2_is_ui12,src2_is_si12,src2_is_si20,src2_is_4)
//   io.src2 := Mux1H(sel_src2, Seq(4.S(32.W), si20_lu12i, si12_sext,ui12_zext, gr_rdk))
//   // pc偏移值offs扩展
//   io.pc_offs := Mux(
//     sign_ext_offs26,
//     Cat(offs26, 0.U(2.W)).asSInt,
//     Cat(offs16, 0.U(2.W)).asSInt
//   )
//   //CSR相关信号
//   io.csr_num_out := inst(23,10)
//   io.wb_csr_out  := inst_frag_decoder.io.cs.wb_csr
//   io.csr_we_out  := inst_frag_decoder.io.cs.csr_we&&io.valid
//   io.csr_open_wmask_out := inst_frag_decoder.io.cs.csr_open_wmask
//   io.ertn_flush_out     := inst_frag_decoder.io.cs.ertn_flush&&io.valid
//   io.cntcontrol_out     := inst_frag_decoder.io.cs.cntcontrol
//   //例外//has_ex,ex_ecode,ex_esubcode
//   when(io.valid){
//     when((~exception(7))&&inst_frag_decoder.io.cs.instNoExist){//INE指令不存在例外
//       io.exception_out:=Cat(1.U(1.W),0xD.U(6.W),0.U(1.W))
//     }.elsewhen((~exception(7))&&inst_frag_decoder.io.cs.ex_break){//BRK断点例外
//       io.exception_out:=Cat(1.U(1.W),0xC.U(6.W),0.U(1.W))
//     }.elsewhen((~exception(7))&&inst_frag_decoder.io.cs.ex_syscall){//SYS系统调用例外
//       io.exception_out:=Cat(1.U(1.W),0xB.U(6.W),0.U(1.W))
//     }.elsewhen((~exception(7))&&io.csr_has_int){//INT中断
//       io.exception_out:=Cat(1.U(1.W),0x0.U(6.W),0.U(1.W))
//     }.otherwise{
//       io.exception_out:=exception
//     }
//   }.otherwise{
//     io.exception_out:=0.U(8.W)
//   }
// }
// class EXE_stage extends Module {
//   val io = IO(new Bundle {
//     val pre_valid = Input(Bool())
//     val next_ready = Input(Bool())
//     val ready = Output(Bool())
//     val valid = Output(Bool())
//     val src1 = Input(SInt(32.W))
//     val src2 = Input(SInt(32.W))
//     val rf_data2 = Input(SInt(32.W))
//     val alu_op = Input(UInt(13.W))
//     val mul_op = Input(UInt(2.W))
//     val div_op = Input(UInt(3.W))
//     val need_divmodule = Output(Bool())
//     val mem_we_in = Input(Bool())
//     val mem_we_out = Output(Bool())
//     val mem_byte_addr = Output(UInt(2.W))
//     val mem_pattern_in = Input(UInt(3.W))
//     val mem_pattern_out = Output(UInt(3.W))
//     val wb_from_mem_in = Input(Bool())
//     val wb_from_mem_out = Output(Bool())
//     val rf_we_in = Input(Bool())
//     val rf_we_out = Output(Bool())
//     val alu_res = Output(SInt(32.W))
//     val mem_addr = Output(UInt(32.W))
//     val mem_data = Output(SInt(32.W))
//     val wb_addr_in = Input(UInt(5.W))
//     val wb_addr_out = Output(UInt(5.W))
//     val pc_in = Input(UInt(32.W))
//     val pc_out = Output(UInt(32.W))
//     val csr_num_in = Input(UInt(14.W))
//     val csr_num_out = Output(UInt(14.W))
//     val wb_csr_in = Input(Bool())
//     val wb_csr_out = Output(Bool())
//     val csr_we_in = Input(Bool())
//     val csr_we_out = Output(Bool())
//     val csr_wmask_out=Output(UInt(32.W))
//     val csr_open_wmask_in = Input(Bool())
//     val csr_open_wmask_out= Output(Bool())
//     val ex_vaddr_out = Output(UInt(32.W))
//     val exception_in = Input(UInt(8.W))//has_ex,ex_ecode,ex_esubcode
//     val exception_out = Output(UInt(8.W))
//     val ertn_flush_in = Input(Bool())
//     val ertn_flush_out = Output(Bool())
//     val clear = Input(Bool())
//     val cntcontrol_in = Input(UInt(3.W))
//     val cntcontrol_out = Output(UInt(3.W))
//   })
//   val ready = Wire(Bool())
//   io.ready := ready
//   val valid = RegInit(false.B)
//   val pc = RegInit(UInt(32.W), 0.U)
//   val wb_addr = RegInit(UInt(5.W), 0.U)
//   val src1 = RegInit(SInt(32.W), 0.S)
//   val src2 = RegInit(SInt(32.W), 0.S)
//   val alu_op = RegInit(UInt(13.W), 0.U)
//   val mul_op = RegInit(UInt(2.W), 0.U)
//   val div_op = RegInit(UInt(3.W), 0.U)

//   val mem_we = RegInit(false.B)
//   val mem_pattern = RegInit(UInt(3.W),0.U)
//   val wb_from_mem = RegInit(false.B)
//   val rf_we = RegInit(false.B)
//   val rf_data2 = RegInit(SInt(32.W), 0.S)

//   val div_sign_ready = RegInit(false.B)
//   val div_unsign_ready = RegInit(false.B)
//   val wb_csr = RegInit(false.B)
//   val csr_num = RegInit(UInt(14.W),0.U)
//   val csr_we = RegInit(false.B)
//   val csr_wmask = RegInit(UInt(32.W), 0.U)
//   val csr_open_wmask = RegInit(false.B)
//   val exception = RegInit(UInt(8.W), 0.U)
//   val ertn_flush = RegInit(false.B)
//   val cntcontrol = RegInit(UInt(3.W), 0.U)
//   when(io.clear){
//     valid:=false.B
//   }
//   .elsewhen(io.pre_valid&&io.ready){
//     valid := true.B
//     pc := io.pc_in
//     wb_addr := io.wb_addr_in

//     alu_op := io.alu_op
//     mul_op := io.mul_op
//     div_op := io.div_op
//     src1 := io.src1
//     src2 := io.src2

//     mem_we := io.mem_we_in
//     mem_pattern:=io.mem_pattern_in
//     wb_from_mem := io.wb_from_mem_in
//     rf_we := io.rf_we_in
//     rf_data2 := io.rf_data2
//     div_sign_ready   := true.B
//     div_unsign_ready := true.B

//     wb_csr:=io.wb_csr_in
//     csr_num:=io.csr_num_in
//     csr_we:=io.csr_we_in
//     csr_open_wmask:=io.csr_open_wmask_in
//     exception:=io.exception_in
//     ertn_flush:=io.ertn_flush_in
//     cntcontrol:=io.cntcontrol_in
//   }.elsewhen(valid&&io.next_ready&&(~div_op(2))){//当是除法指令时阻塞
//     valid := false.B
//   }

//   io.valid := valid&io.ready
//   io.pc_out := pc 
//   io.wb_addr_out := wb_addr


//   io.mem_we_out := mem_we && valid && (~io.exception_out(7))//需要无异常
//   io.mem_pattern_out := mem_pattern
//   io.wb_from_mem_out := wb_from_mem
//   io.rf_we_out := rf_we && valid

//   val alu = Module(new ALU())
//   alu.io.alu_op := alu_op
//   alu.io.mul_op:=mul_op
//   alu.io.src1 := src1
//   alu.io.src2 := src2
//   io.mem_addr := alu.io.mem_addr
//   io.mem_byte_addr:=alu.io.mem_addr(1,0)
//   io.mem_data := rf_data2

//   // io.cs.div_op := Cat(need_divmodule,div_or_mod,div_sign_unsign)
//   val need_divmodule = div_op(2)&valid
//   val div_or_mod     = div_op(1)
//   val div_sign_unsign= div_op(0)
//   val div_sign = Module(new div_sign())
//   val div_unsign = Module(new div_unsign())
//   //有符号除法
//   div_sign.io.aclk:=clock
//   div_sign.io.s_axis_dividend_tdata:=src1
//   div_sign.io.s_axis_divisor_tdata:=src2
//   when(need_divmodule&div_sign.io.s_axis_dividend_tready&&div_sign.io.s_axis_divisor_tready){div_sign_ready:=false.B}
//   div_sign.io.s_axis_divisor_tvalid:=need_divmodule&div_sign_ready
//   div_sign.io.s_axis_dividend_tvalid:=need_divmodule&div_sign_ready
//   val div_sign_res = div_sign.io.m_axis_dout_tdata
//   //无符号除法
//   div_unsign.io.aclk:=clock
//   div_unsign.io.s_axis_dividend_tdata:=src1.asUInt
//   div_unsign.io.s_axis_divisor_tdata:=src2.asUInt
//   when(need_divmodule&div_unsign.io.s_axis_dividend_tready&div_unsign.io.s_axis_divisor_tready){div_unsign_ready:=false.B}
//   div_unsign.io.s_axis_divisor_tvalid :=need_divmodule&div_unsign_ready
//   div_unsign.io.s_axis_dividend_tvalid:=need_divmodule&div_unsign_ready
//   val div_unsign_res = div_unsign.io.m_axis_dout_tdata
//   //有无符号选择
//   val divmod_res = Mux(div_sign_unsign,div_sign_res,div_unsign_res)
//   val div_res = Mux(div_or_mod,divmod_res(63,32).asSInt,divmod_res(31,0).asSInt)
//   io.alu_res := Mux(need_divmodule,div_res,alu.io.alu_res)
//   val div_res_valid = Mux(div_sign_unsign,div_sign.io.m_axis_dout_tvalid,div_unsign.io.m_axis_dout_tvalid)
//   ready:=(need_divmodule&div_res_valid)|(~need_divmodule)
//   io.need_divmodule:=need_divmodule&(~div_res_valid)
//   //CSR
//   io.wb_csr_out:=wb_csr
//   io.csr_num_out:=csr_num
//   io.csr_we_out:=csr_we&& valid
//   io.csr_wmask_out:=src1.asUInt
//   io.csr_open_wmask_out:=csr_open_wmask
//   io.ex_vaddr_out:=io.mem_addr
//   io.ertn_flush_out:=ertn_flush&&io.valid
//   io.cntcontrol_out:=cntcontrol
//   //例外
//   val mem_addr_err = Wire(Bool())//地址非对齐
//   when(io.valid){
//     when((~exception(7))&&mem_addr_err){//还未标记异常,当前有异常
//       io.exception_out:=Cat(1.U(1.W),0x9.U(6.W),0.U(1.W))
//     }.otherwise{
//       io.exception_out:=exception
//     }
//   }.otherwise{
//     io.exception_out:=0.U(8.W)
//   }
//   //访存地址错误
//   //wb_from_mem_out
//   //mem_we_out
//   val mem_is_w=io.mem_pattern_out(2)
//   val mem_b_h =io.mem_pattern_out(1)
//   val mem_s_u =io.mem_pattern_out(0)
//   //mem_addr_err地址非对齐
//   when(io.valid&&(io.wb_from_mem_out|mem_we)){//读内存或写内存
//     when(mem_is_w&(io.mem_addr(1,0)=/=0.U)){//4字节,最低2位非0
//       mem_addr_err:=true.B
//     }.elsewhen((!mem_b_h)&io.mem_addr(0)){//2字节,最低位非0
//       mem_addr_err:=true.B
//     }.otherwise{mem_addr_err:=false.B}
//   }.otherwise{mem_addr_err:=false.B}

// }
// class MEM_stage extends Module {
//   val io = IO(new Bundle {
//     val pre_valid = Input(Bool())
//     val next_ready = Input(Bool())
//     val ready = Output(Bool())
//     val valid = Output(Bool())
//     val alu_res = Input(SInt(32.W))
//     val wb_data = Output(SInt(32.W))
//     val mem_byte_addr = Input(UInt(2.W))
//     val mem_pattern_in = Input(UInt(3.W))
//     val wb_from_mem = Input(Bool())
//     val mem_value = Input(SInt(32.W))
//     val rf_we_in = Input(Bool())
//     val rf_we_out = Output(Bool())
//     val wb_addr_in = Input(UInt(5.W))
//     val wb_addr_out = Output(UInt(5.W))
//     val pc_in = Input(UInt(32.W))
//     val pc_out = Output(UInt(32.W))
//     val csr_num_in = Input(UInt(14.W))
//     val csr_num_out = Output(UInt(14.W))
//     val wb_csr_in = Input(Bool())
//     val wb_csr_out = Output(Bool())
//     val csr_we_in = Input(Bool())
//     val csr_we_out = Output(Bool())
//     val rd_data_in = Input(UInt(32.W))
//     val rd_data_out = Output(UInt(32.W))
//     val csr_wmask_in =Input(UInt(32.W))
//     val csr_wmask_out=Output(UInt(32.W))
//     val csr_open_wmask_in = Input(Bool())
//     val csr_open_wmask_out= Output(Bool())
//     val ex_vaddr_in = Input(UInt(32.W))
//     val ex_vaddr_out = Output(UInt(32.W))
//     val exception_in = Input(UInt(8.W))//has_ex,ex_ecode,ex_esubcode
//     val exception_out = Output(UInt(8.W))
//     val ertn_flush_in = Input(Bool())
//     val ertn_flush_out = Output(Bool())
//     val clear = Input(Bool())
//     val cntcontrol_in = Input(UInt(3.W))
//     val cntcontrol_out = Output(UInt(3.W))
//   })
//   io.ready := true.B
//   val valid = RegInit(false.B)
//   val pc = RegInit(UInt(32.W), 0.U)
//   val wb_addr = RegInit(UInt(5.W), 0.U)
//   val alu_res = RegInit(SInt(32.W), 0.S)
//   val mem_byte_addr = RegInit(UInt(2.W), 0.U)
//   val mem_pattern = RegInit(UInt(3.W), 0.U)
//   val rf_we = RegInit(false.B)
//   val wb_from_mem = RegInit(false.B)
//   val wb_csr = RegInit(false.B)
//   val csr_num = RegInit(UInt(14.W),0.U)
//   val rd_data = RegInit(UInt(32.W),0.U)
//   val csr_we = RegInit(false.B)
//   val csr_wmask = RegInit(UInt(32.W), 0.U)
//   val csr_open_wmask = RegInit(false.B)
//   val ex_vaddr = RegInit(UInt(32.W), 0.U)
//   val exception = RegInit(UInt(8.W), 0.U)
//   val ertn_flush=RegInit(false.B)
//   val cntcontrol = RegInit(UInt(3.W), 0.U)
//   when(io.clear){
//     valid:=false.B
//   }.elsewhen(io.pre_valid&&io.ready){
//     valid := true.B
//     pc := io.pc_in
//     wb_addr := io.wb_addr_in
//     alu_res := io.alu_res
//     rf_we := io.rf_we_in
//     wb_from_mem := io.wb_from_mem
//     mem_byte_addr:=io.mem_byte_addr
//     mem_pattern:=io.mem_pattern_in
//     wb_csr:=io.wb_csr_in
//     csr_num:=io.csr_num_in
//     rd_data:=io.rd_data_in
//     csr_we:=io.csr_we_in
//     csr_wmask:=io.csr_wmask_in
//     csr_open_wmask:=io.csr_open_wmask_in
//     exception:=io.exception_in
//     ertn_flush:=io.ertn_flush_in
//     ex_vaddr:=io.ex_vaddr_in
//     cntcontrol:=io.cntcontrol_in
//   }.elsewhen(valid&&io.next_ready){
//     valid:=false.B
//   }
//   io.valid := valid
//   io.pc_out := pc
//   io.wb_addr_out := wb_addr
//   io.rf_we_out := rf_we && valid
//   // io.cs.mem_pattern:= Cat(mem_is_w,mem_b_h,mem_s_u)
//   val mem_is_w=mem_pattern(2)
//   val mem_b_h =mem_pattern(1)
//   val mem_s_u =mem_pattern(0)
//   val byte = Mux(mem_byte_addr(1),Mux(mem_byte_addr(0),io.mem_value(31,24),io.mem_value(23,16))
//                                  ,Mux(mem_byte_addr(0),io.mem_value(15,8),io.mem_value(7,0)))
//   val halfword = Mux(mem_byte_addr(1),io.mem_value(31,16),io.mem_value(15,0))
//   val byte_ext = Mux(mem_s_u,byte.asSInt,Cat(0.U(24.W),byte).asSInt)
//   val halfword_ext =Mux(mem_s_u,halfword.asSInt,Cat(0.U(12.W),halfword).asSInt)
//   val mem_ext = Mux(mem_b_h,byte_ext,halfword_ext)
//   val mem_res = Mux(mem_is_w,io.mem_value,mem_ext)

//   io.wb_data := Mux(wb_from_mem, mem_res, alu_res)
//   io.wb_csr_out:=wb_csr
//   io.csr_num_out:=csr_num
//   io.rd_data_out:=rd_data
//   io.csr_we_out:=csr_we && valid
//   io.csr_wmask_out:=csr_wmask
//   io.csr_open_wmask_out:=csr_open_wmask
//   io.ex_vaddr_out:=ex_vaddr
//   io.ertn_flush_out:=ertn_flush&&io.valid
//   io.cntcontrol_out:=cntcontrol
//   //例外
//   when(io.valid){
//     io.exception_out:=exception
//   }.otherwise{
//     io.exception_out:=0.U(8.W)
//   }
// }
// class WB_stage extends Module {
//   val io = IO(new Bundle {
//     val pre_valid = Input(Bool())
//     val next_ready = Input(Bool())
//     val ready = Output(Bool())
//     val valid = Output(Bool())
//     val wb_data_in = Input(SInt(32.W))
//     val wb_data_out = Output(SInt(32.W))
//     val rf_we_in = Input(Bool())
//     val rf_we_out = Output(Bool())
//     val wb_addr_in = Input(UInt(5.W))
//     val wb_addr_out = Output(UInt(5.W))
//     val pc_in = Input(UInt(32.W))
//     val pc_out = Output(UInt(32.W))
//     val csr_num_in = Input(UInt(14.W))
//     val csr_num_out = Output(UInt(14.W))
//     val wb_csr_in = Input(Bool())
//     val wb_csr_out = Output(Bool())
//     val csr_we_in = Input(Bool())
//     val csr_we_out = Output(Bool())
//     val csr_has_int = Output(Bool())
//     val rd_data_in = Input(UInt(32.W))
//     val csr_wmask_in=Input(UInt(32.W))
//     val csr_open_wmask_in = Input(Bool())
//     val ex_vaddr_in = Input(UInt(32.W))
//     val exception_in = Input(UInt(8.W))//has_ex,ex_ecode,ex_esubcode
//     val exception_out = Output(UInt(8.W))//has_ex,ex_ecode,ex_esubcode
//     val clearpipline = Output(Bool())
//     val csr_pc = Output(UInt(32.W))
//     val ertn_flush_in = Input(Bool())
//     val ertn_flush_out = Output(Bool())
//     val clear = Input(Bool())
//     val cntcontrol_in = Input(UInt(3.W))
//     val cntcontrol_out = Output(UInt(3.W))
//   })
//   //计时器
//   val stable_counter = RegInit(UInt(64.W), 0.U)
//   stable_counter:=stable_counter+1.U
//   io.ready := true.B
//   val valid = RegInit(false.B)
//   val pc = RegInit(UInt(32.W), 0.U)
//   val wb_data = RegInit(SInt(32.W), 0.S)
//   val wb_addr = RegInit(UInt(32.W), 0.U)
//   val rf_we = RegInit(false.B)
//   val wb_csr = RegInit(false.B)
//   val csr_num = RegInit(UInt(14.W),0.U)
//   val rd_data = RegInit(UInt(32.W),0.U)
//   val csr_we = RegInit(false.B)
//   val csr_wmask = RegInit(UInt(32.W), 0.U)
//   val csr_open_wmask = RegInit(false.B)
//   val ex_vaddr = RegInit(UInt(32.W), 0.U)
//   val exception = RegInit(UInt(8.W), 0.U)
//   val ertn_flush=RegInit(false.B)
//   val cntcontrol = RegInit(UInt(3.W), 0.U)
//   when(io.clear){
//     valid:=false.B
//   }.elsewhen(io.pre_valid&&io.ready){
//     valid := true.B
//     pc := io.pc_in
//     wb_data := io.wb_data_in
//     wb_addr := io.wb_addr_in
//     rf_we := io.rf_we_in
//     wb_csr:=io.wb_csr_in
//     csr_num:=io.csr_num_in
//     rd_data:=io.rd_data_in
//     csr_we:=io.csr_we_in
//     csr_wmask:=io.csr_wmask_in
//     csr_open_wmask:=io.csr_open_wmask_in
//     exception:=io.exception_in
//     ertn_flush:=io.ertn_flush_in
//     ex_vaddr:=io.ex_vaddr_in
//     cntcontrol:=io.cntcontrol_in
//   }.elsewhen(valid&&io.next_ready){
//     valid:=false.B
//   }
//   io.valid := valid
//   io.pc_out := pc
//   val csr = Module(new CSR())
//   csr.io.csr_num := csr_num
//   csr.io.csr_we:=csr_we&&valid
//   csr.io.csr_wmask:=Mux(csr_open_wmask,csr_wmask,0xffffffffL.U(32.W))
//   csr.io.csr_wvalue:=rd_data
//   csr.io.hw_int_in:=0.U(8.W)//8个硬中断暂时认为为0
//   csr.io.ipi_int_in:=0.U(1.W)//无核间中断
//   csr.io.ex_pc:=pc
//   csr.io.ex_vaddr:=ex_vaddr
//   //has_ex,ex_ecode,ex_esubcode
//   csr.io.csr_ertn_flush:=ertn_flush&&valid
//   csr.io.csr_wb_ex:=exception(7)&&valid
//   csr.io.csr_wb_ecode:=exception(6,1)
//   csr.io.csr_wb_esubcode:=Cat(0.U(8.W),exception(0))
//   //io.cs.cntcontrol:=Cat(time_counter_l_h,timecnt_tid,wb_about_timedata)
//   val timelh = Mux(cntcontrol(2),stable_counter(31,0),stable_counter(63,32))
//   val timedata = Mux(cntcontrol(1),timelh,csr.io.csr_tid)
//   io.wb_data_out := Mux(wb_csr,csr.io.csr_rvalue.asSInt,Mux(cntcontrol(0),timedata.asSInt,wb_data))
//   io.wb_addr_out := wb_addr
//   io.rf_we_out := rf_we&&valid&&(~exception(7))
//   io.csr_num_out:=csr_num
//   io.csr_we_out:=csr_we&&valid&&(~exception(7))
//   io.wb_csr_out:=wb_csr
//   io.csr_has_int:=csr.io.csr_has_int
//   io.clearpipline:=(exception(7)|ertn_flush)&&valid//例外或者ertn清空流水线
//   io.ertn_flush_out:=ertn_flush&&io.valid
//   io.cntcontrol_out:=cntcontrol
//   io.csr_pc:=Mux(io.ertn_flush_out,csr.io.csr_era,csr.io.csr_ex_entry)
//   //例外
//   when(io.valid){
//     io.exception_out:=exception
//   }.otherwise{
//     io.exception_out:=0.U(8.W)
//   }
// }
// class minicpu_top_pipline extends Module {
//   val io = IO(new Bundle {
//     val inst_sram_en = Output(Bool())
//     val inst_sram_we = Output(UInt(4.W))
//     val inst_sram_addr = Output(UInt(32.W))
//     val inst_sram_wdata = Output(UInt(32.W))
//     val inst_sram_rdata = Input(UInt(32.W))

//     val data_sram_en = Output(Bool())
//     val data_sram_we = Output(UInt(4.W))
//     val data_sram_addr = Output(UInt(32.W))
//     val data_sram_wdata = Output(SInt(32.W))
//     val data_sram_rdata = Input(SInt(32.W))

//     val debug_wb_pc = Output(UInt(32.W))
//     val debug_wb_rf_we = Output(UInt(4.W))
//     val debug_wb_rf_wnum = Output(UInt(5.W))
//     val debug_wb_rf_wdata = Output(SInt(32.W))
//   })
//   val pre_if = Module(new pre_IF())
//   val if_stage = Module(new IF_stage())
//   val exe_stage = Module(new EXE_stage())
//   val mem_stage = Module(new MEM_stage())
//   val wb_stage = Module(new WB_stage())
//   ////////////////
//   //// 取指阶段////
//   ////////////////
//   if_stage.io.nextpc := pre_if.io.nextpc
//   //cpu取指
//   io.inst_sram_en := true.B
//   io.inst_sram_we := 0.U
//   io.inst_sram_addr := if_stage.io.inst_sram_addr
//   io.inst_sram_wdata := 0.U
//   if_stage.io.inst_sram_rdata := io.inst_sram_rdata
//   ////////////////
//   // 译码阶段
//   ////////////////
//   val id_stage = Module(new ID_stage())
//   id_stage.io.pre_valid := if_stage.io.valid
//   id_stage.io.inst := if_stage.io.inst
//   id_stage.io.pc_in := if_stage.io.pc
//   id_stage.io.csr_has_int:=wb_stage.io.csr_has_int
//   id_stage.io.exception_in:=if_stage.io.exception_out
//   pre_if.io.base_pc_from_rj := id_stage.io.base_pc_from_rj
//   pre_if.io.offs_ext := id_stage.io.pc_offs
//   pre_if.io.gr_rj := id_stage.io.rf_data1
//   pre_if.io.pc := id_stage.io.pc_out
//   if_stage.io.br_taken:=id_stage.io.br_taken
//   ////////////////
//   // 执行阶段EXE
//   ////////////////
//   exe_stage.io.pre_valid := id_stage.io.valid
//   exe_stage.io.src1 := id_stage.io.src1
//   exe_stage.io.src2 := id_stage.io.src2
//   exe_stage.io.rf_data2 := id_stage.io.rf_data2
//   exe_stage.io.alu_op := id_stage.io.alu_op
//   exe_stage.io.mul_op := id_stage.io.mul_op
//   exe_stage.io.div_op := id_stage.io.div_op
//   exe_stage.io.mem_we_in := id_stage.io.mem_we
//   exe_stage.io.mem_pattern_in:=id_stage.io.mem_pattern
//   exe_stage.io.wb_from_mem_in := id_stage.io.wb_from_mem
//   exe_stage.io.rf_we_in := id_stage.io.rf_we_ID
//   exe_stage.io.wb_addr_in := id_stage.io.wb_addr_out
//   exe_stage.io.pc_in := id_stage.io.pc_out
//   exe_stage.io.csr_num_in:=id_stage.io.csr_num_out
//   exe_stage.io.wb_csr_in:=id_stage.io.wb_csr_out
//   exe_stage.io.csr_we_in:=id_stage.io.csr_we_out
//   exe_stage.io.csr_open_wmask_in:=id_stage.io.csr_open_wmask_out
//   exe_stage.io.exception_in:=id_stage.io.exception_out
//   exe_stage.io.ertn_flush_in:=id_stage.io.ertn_flush_out
//   exe_stage.io.cntcontrol_in:=id_stage.io.cntcontrol_out
//   ////////////////
//   // 访存阶段MEM_Stage
//   ////////////////
//   mem_stage.io.pre_valid := exe_stage.io.valid
//   mem_stage.io.alu_res := exe_stage.io.alu_res
//   mem_stage.io.wb_from_mem := exe_stage.io.wb_from_mem_out
//   mem_stage.io.mem_byte_addr :=exe_stage.io.mem_byte_addr
//   mem_stage.io.mem_pattern_in   :=exe_stage.io.mem_pattern_out//Cat(mem_is_w,mem_b_h,mem_s_u)

//   io.data_sram_en := true.B
//   val mem_is_w = exe_stage.io.mem_pattern_out(2)
//   val mem_b_h = exe_stage.io.mem_pattern_out(1)
//   val byte_addr=  exe_stage.io.mem_addr(1,0)
//   val rd_data = exe_stage.io.mem_data
//   val st_data = Mux(mem_is_w,rd_data,
//                              Mux(mem_b_h,Cat(rd_data(7,0),rd_data(7,0),rd_data(7,0),rd_data(7,0)).asSInt
//                                  ,Cat(rd_data(15,0),rd_data(15,0)).asSInt))
//   val data_sram_we = Wire(UInt(4.W))
//   when(exe_stage.io.mem_we_out&&(~mem_stage.io.exception_out(7))&&(~wb_stage.io.exception_out(7))&&
//                                 (~mem_stage.io.ertn_flush_out)&&(~wb_stage.io.ertn_flush_out)){
//     when(mem_is_w){
//       data_sram_we:=0b1111.U
//     }.elsewhen(mem_b_h){
//       data_sram_we:=Mux(byte_addr(1),Mux(byte_addr(0),0b1000.U,0b0100.U),
//                                      Mux(byte_addr(0),0b0010.U,0b0001.U))
//     }.otherwise{//halfword
//       data_sram_we:=Mux(byte_addr(1),0b1100.U,0b0011.U)
//     }
//   }.otherwise{
//     data_sram_we:=0b0000.U
//   }
//   io.data_sram_we := data_sram_we
//   io.data_sram_addr := exe_stage.io.mem_addr
//   io.data_sram_wdata := st_data

//   mem_stage.io.mem_value := io.data_sram_rdata
//   mem_stage.io.rf_we_in := exe_stage.io.rf_we_out
//   mem_stage.io.wb_addr_in := exe_stage.io.wb_addr_out
//   mem_stage.io.pc_in := exe_stage.io.pc_out
//   mem_stage.io.csr_num_in:=exe_stage.io.csr_num_out
//   mem_stage.io.wb_csr_in:=exe_stage.io.wb_csr_out
//   mem_stage.io.csr_we_in:=exe_stage.io.csr_we_out
//   mem_stage.io.rd_data_in:=exe_stage.io.mem_data.asUInt
//   mem_stage.io.csr_wmask_in:=exe_stage.io.csr_wmask_out
//   mem_stage.io.csr_open_wmask_in:=exe_stage.io.csr_open_wmask_out
//   mem_stage.io.exception_in:=exe_stage.io.exception_out
//   mem_stage.io.ertn_flush_in:=exe_stage.io.ertn_flush_out
//   mem_stage.io.ex_vaddr_in:=exe_stage.io.ex_vaddr_out
//   mem_stage.io.cntcontrol_in:=exe_stage.io.cntcontrol_out
//   ////////////////
//   // 写回阶段WB_Stage
//   ////////////////
//   wb_stage.io.pre_valid := mem_stage.io.valid
//   wb_stage.io.wb_data_in := mem_stage.io.wb_data
//   wb_stage.io.rf_we_in := mem_stage.io.rf_we_out
//   wb_stage.io.wb_addr_in := mem_stage.io.wb_addr_out
//   wb_stage.io.pc_in := mem_stage.io.pc_out
//   wb_stage.io.csr_num_in:=mem_stage.io.csr_num_out
//   wb_stage.io.wb_csr_in:=mem_stage.io.wb_csr_out
//   wb_stage.io.csr_we_in:=mem_stage.io.csr_we_out 
//   wb_stage.io.rd_data_in:=mem_stage.io.rd_data_out
//   wb_stage.io.csr_wmask_in:=mem_stage.io.csr_wmask_out
//   wb_stage.io.csr_open_wmask_in:=mem_stage.io.csr_open_wmask_out
//   wb_stage.io.exception_in:=mem_stage.io.exception_out
//   wb_stage.io.ertn_flush_in:=mem_stage.io.ertn_flush_out
//   wb_stage.io.ex_vaddr_in:=mem_stage.io.ex_vaddr_out
//   wb_stage.io.cntcontrol_in:=mem_stage.io.cntcontrol_out
//   val wb_rf_we = wb_stage.io.rf_we_out
//   id_stage.io.rf_we_WB := wb_stage.io.rf_we_out
//   id_stage.io.wb_data := wb_stage.io.wb_data_out
//   id_stage.io.wb_addr_in := wb_stage.io.wb_addr_out
//   if_stage.io.csr_pc:=wb_stage.io.csr_pc
//   if_stage.io.csr_pc_taken:=wb_stage.io.exception_out(7)||wb_stage.io.ertn_flush_out//触发例外或ertn
  
//   //debug信号
//   io.debug_wb_pc := wb_stage.io.pc_out
//   io.debug_wb_rf_we := Cat(wb_rf_we, wb_rf_we, wb_rf_we, wb_rf_we)
//   io.debug_wb_rf_wnum := wb_stage.io.wb_addr_out
//   io.debug_wb_rf_wdata := wb_stage.io.wb_data_out
//   // valid和ready信号传递
//   if_stage.io.pre_valid:=true.B
//   if_stage.io.next_ready:=id_stage.io.ready
  
//   id_stage.io.pre_valid:=if_stage.io.valid
//   id_stage.io.next_ready:=exe_stage.io.ready
//   id_stage.io.clear:=wb_stage.io.clearpipline

//   exe_stage.io.pre_valid:=id_stage.io.valid
//   exe_stage.io.next_ready:=mem_stage.io.ready
//   exe_stage.io.clear:=wb_stage.io.clearpipline

//   mem_stage.io.pre_valid:=exe_stage.io.valid
//   mem_stage.io.next_ready:=wb_stage.io.ready
//   mem_stage.io.clear:=wb_stage.io.clearpipline

//   wb_stage.io.pre_valid:=mem_stage.io.valid
//   wb_stage.io.next_ready:=true.B
//   wb_stage.io.clear:=wb_stage.io.clearpipline
//   //阻塞控制
//   val block_judge = Module(new Block_Judge())
//   block_judge.io.need_rf_raddr1:=id_stage.io.need_rf_raddr1
//   block_judge.io.need_rf_raddr2:=id_stage.io.need_rf_raddr2

//   block_judge.io.rf_raddr1:=id_stage.io.rf_raddr1
//   block_judge.io.rf_rdata1:=id_stage.io.to_forward_rf_data1
//   block_judge.io.rf_raddr2:=id_stage.io.rf_raddr2
//   block_judge.io.rf_rdata2:=id_stage.io.to_forward_rf_data2

//   block_judge.io.exe_wb_from_mem:=exe_stage.io.wb_from_mem_out
//   block_judge.io.exe_rf_we   :=exe_stage.io.rf_we_out
//   block_judge.io.exe_rf_waddr:=exe_stage.io.wb_addr_out
//   block_judge.io.exe_alu_res:=exe_stage.io.alu_res
//   block_judge.io.exe_wb_csr:=exe_stage.io.wb_csr_out
//   block_judge.io.exe_wb_timedata:=exe_stage.io.cntcontrol_out(0)

//   block_judge.io.mem_rf_we   :=mem_stage.io.rf_we_out
//   block_judge.io.mem_rf_waddr:=mem_stage.io.wb_addr_out
//   block_judge.io.mem_wb_data:=mem_stage.io.wb_data
//   block_judge.io.mem_wb_csr:=mem_stage.io.wb_csr_out
//   block_judge.io.mem_wb_timedata:=mem_stage.io.cntcontrol_out(0)

//   block_judge.io.wb_rf_we    :=wb_stage.io.rf_we_out
//   block_judge.io.wb_rf_waddr :=wb_stage.io.wb_addr_out
//   block_judge.io.wb_wb_data:=wb_stage.io.wb_data_out
//   block_judge.io.wb_wb_csr:=wb_stage.io.wb_csr_out
//   block_judge.io.wb_wb_timedata:=wb_stage.io.cntcontrol_out(0)

//   if_stage.io.needBlock:=(block_judge.io.needBlock|exe_stage.io.need_divmodule)&&(~wb_stage.io.clearpipline)
//   id_stage.io.needBlock:=(block_judge.io.needBlock|exe_stage.io.need_divmodule)&&(~wb_stage.io.clearpipline)
//   id_stage.io.forward_rf_rdata1:=block_judge.io.forward_rf_rdata1
//   id_stage.io.forward_rf_rdata2:=block_judge.io.forward_rf_rdata2
// }
