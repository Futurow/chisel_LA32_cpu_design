import chisel3._
import chisel3.util._
//必须有一个object不然之后sbt run的时候会报错发现不了一个main，这段话的意思是生成一个Verilog程序，在这里我感觉和chisel-bootcamp中jupyter里不太一样（chisel-bootcamp是Git一个项目适合初学者学习chisel，可以去看看）
object res extends App {
  // emitVerilog(new minicpu_top_5inst(), Array("--target-dir", "generated"))
  // emitVerilog(new RegFile(), Array("--target-dir", "generated"))
  // emitVerilog(new Inst_Frag_Decoder(), Array("--target-dir", "generated"))
  // emitVerilog(
  //   new minicpu_top_pipline(),
  //   Array("--target-dir", "D:/Code/VScode/cdp_ede_local/mycpu_env/myCPU")
  // )
  emitVerilog(
    new minicpu_top_pipline(),
    Array("--target-dir", "generated")
  )
}
