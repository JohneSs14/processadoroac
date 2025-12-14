`timescale 1ns / 1ps
//=============
//|           |
//|           |
//|           |
//|           |
//=============
// riscvsingle.sv

// RISC-V single-cycle processor
// From Section 7.6 of Digital Design & Computer Architecture
// 27 April 2020
// David_Harris@hmc.edu 
// Sarah.Harris@unlv.edu

// run 210
// Expect simulator to print "Simulation succeeded"
// when the value 25 (0x19) is written to address 100 (0x64)

// Single-cycle implementation of RISC-V (RV32I)
// User-level Instruction Set Architecture V2.2 (May 7, 2017)
// Implements a subset of the base integer instructions:
//    lw, sw
//    add, sub, and, or, slt, 
//    addi, andi, ori, slti
//    beq
//    jal
// Exceptions, traps, and interrupts not implemented
// little-endian memory

// 31 32-bit registers x1-x31, x0 hardwired to 0
// R-Type instructions
//   add, sub, and, or, slt
//   INSTR rd, rs1, rs2
//   Instr[31:25] = funct7 (funct7b5 & opb5 = 1 for sub, 0 for others)
//   Instr[24:20] = rs2
//   Instr[19:15] = rs1
//   Instr[14:12] = funct3
//   Instr[11:7]  = rd
//   Instr[6:0]   = opcode
// I-Type Instructions
//   lw, I-type ALU (addi, andi, ori, slti)
//   lw:         INSTR rd, imm(rs1)
//   I-type ALU: INSTR rd, rs1, imm (12-bit signed)
//   Instr[31:20] = imm[11:0]
//   Instr[24:20] = rs2
//   Instr[19:15] = rs1
//   Instr[14:12] = funct3
//   Instr[11:7]  = rd
//   Instr[6:0]   = opcode
// S-Type Instruction
//   sw rs2, imm(rs1) (store rs2 into address specified by rs1 + immm)
//   Instr[31:25] = imm[11:5] (offset[11:5])
//   Instr[24:20] = rs2 (src)
//   Instr[19:15] = rs1 (base)
//   Instr[14:12] = funct3
//   Instr[11:7]  = imm[4:0]  (offset[4:0])
//   Instr[6:0]   = opcode
// B-Type Instruction
//   beq rs1, rs2, imm (PCTarget = PC + (signed imm x 2))
//   Instr[31:25] = imm[12], imm[10:5]
//   Instr[24:20] = rs2
//   Instr[19:15] = rs1
//   Instr[14:12] = funct3
//   Instr[11:7]  = imm[4:1], imm[11]
//   Instr[6:0]   = opcode
// J-Type Instruction
//   jal rd, imm  (signed imm is multiplied by 2 and added to PC, rd = PC+4)
//   Instr[31:12] = imm[20], imm[10:1], imm[11], imm[19:12]
//   Instr[11:7]  = rd
//   Instr[6:0]   = opcode

//   Instruction  opcode    funct3    funct7
//   add          0110011   000       0000000
//   sub          0110011   000       0100000
//   and          0110011   111       0000000
//   or           0110011   110       0000000
//   slt          0110011   010       0000000
//   addi         0010011   000       immediate
//   andi         0010011   111       immediate
//   ori          0010011   110       immediate
//   slti         0010011   010       immediate
//   beq          1100011   000       immediate
//   lw	          0000011   010       immediate
//   sw           0100011   010       immediate
//   jal          1101111   immediate immediate

module testbench();

  logic        clk;
  logic        reset;

  logic [31:0] WriteData, DataAdr;
  logic        MemWrite;

  // instantiate device to be tested
  top dut(clk, reset, WriteData, DataAdr, MemWrite);
  
  // initialize test
  initial
    begin
      reset <= 1; # 22; reset <= 0;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
     
    end

  // check results
  always @(negedge clk)
    begin
       $display("Time: %5d, PC: %4h, Instr: %8h, MemWrite: %4b, DataAdr: %4h, WriteData: %4h, Rs2: %8h, PCSrc: %1b, PCTarget_MEM: %8h, PCTarget: %8h, Branch_MEM: %1b, Jump_MEM: %1b, Zero_MEM: %1b, SrcA_final: %8h, SrcB: %8h, AluResult_MEM: %8h, UlaA: %2b, UlaB: %2b, ALUResult: %8h, ALUSrc_EX: %1b, ImmExt_EX: %8h, ImmExt: %8h, SrcB_final: %8h, Instr_ID: %8h, MainDecOp: %7b, ALUControl: %3b, Branch: %1b, Jump: %1b, PCNext: %32b, Zero: %1b, Rd_WB: %8h, Result: %8h, RegWrite_WB: %1b, wd3: %8h \n\n",
               $time, dut.rvsingle.PC, dut.rvsingle.Instr, MemWrite, DataAdr, dut.rvsingle.dp.WriteData, dut.rvsingle.dp.Instr_ID[24:20], dut.rvsingle.PCSrc, dut.rvsingle.dp.PCTarget_MEM, dut.rvsingle.dp.PCTarget, dut.rvsingle.dp.Branch_MEM, dut.rvsingle.dp.Jump_MEM, dut.rvsingle.dp.Zero_MEM, dut.rvsingle.dp.SrcA_final, dut.rvsingle.dp.SrcB, dut.rvsingle.dp.ALUResult_MEM, dut.rvsingle.dp.UlaA, dut.rvsingle.dp.UlaB, dut.rvsingle.dp.ALUResult, dut.rvsingle.dp.ALUSrc_EX, dut.rvsingle.dp.ImmExt_EX, dut.rvsingle.dp.ImmExt, dut.rvsingle.dp.SrcB_final, dut.rvsingle.dp.Instr_ID, 
               dut.rvsingle.c.md.op, dut.rvsingle.dp.ALUControl, dut.rvsingle.dp.Branch, dut.rvsingle.dp.Jump, dut.rvsingle.dp.PCNext, dut.rvsingle.dp.Zero, dut.rvsingle.dp.Rd_WB, dut.rvsingle.dp.Result, dut.rvsingle.dp.RegWrite_WB, dut.rvsingle.dp.rf.wd3);
      if(MemWrite) begin
        if(DataAdr === 100 & WriteData === 25) begin
          $display("Simulation succeeded");
          $stop;
        end else if (DataAdr !== 96) begin
          $display("Simulation failed");
          $stop;
        end
      end
    end
endmodule

module top(input  logic        clk, reset, 
           output logic [31:0] WriteData, DataAdr, 
           output logic        MemWrite);

  logic [31:0] PC, Instr, ReadData;
  
  // instantiate processor and memories
  riscvsingle rvsingle(clk, reset, PC, Instr, MemWrite, DataAdr, 
                       WriteData, ReadData);
  imem imem(PC, Instr);
  dmem dmem(clk, MemWrite, DataAdr, WriteData, ReadData);
endmodule

module riscvsingle(input  logic        clk, reset,
                   output logic [31:0] PC,
                   input  logic [31:0] Instr,
                   output logic        MemWrite_MEM,
                   output logic [31:0] ALUResult, WriteData,
                   input  logic [31:0] ReadData);

  logic       ALUSrc, RegWrite, Jump, Zero, Branch, MemWrite;
  logic [1:0] ResultSrc, ImmSrc;
  logic [2:0] ALUControl;

  logic [31:0] Instr_ID;

  controller c(Instr_ID[6:0], Instr_ID[14:12], Instr_ID[30], Zero,
               ResultSrc, MemWrite, PCSrc,
               ALUSrc, RegWrite, Jump,
               ImmSrc, ALUControl, Branch, Branch_MEM, Jump_MEM);
  datapath dp(clk, reset, ResultSrc, PCSrc,
              ALUSrc, RegWrite,
              ImmSrc, ALUControl,
              Zero, PC, Instr, Instr_ID,
              ALUResult, WriteData, ReadData, Branch, Jump, MemWrite, Branch_MEM, Jump_MEM, MemWrite_MEM);
endmodule

module controller(input  logic [6:0] op,
                  input  logic [2:0] funct3,
                  input  logic       funct7b5,
                  input  logic       Zero_MEM,
                  output logic [1:0] ResultSrc,
                  output logic       MemWrite,
                  output logic       PCSrc, ALUSrc,
                  output logic       RegWrite, Jump,
                  output logic [1:0] ImmSrc,
                  output logic [2:0] ALUControl,
                  
                  output logic       Branch,

                  input logic        Branch_MEM,
                  input logic        Jump_MEM
                  );

  logic [1:0] ALUOp;

  maindec md(op, ResultSrc, MemWrite, Branch,
             ALUSrc, RegWrite, Jump, ImmSrc, ALUOp);
  aludec  ad(op[5], funct3, funct7b5, ALUOp, ALUControl);

  assign PCSrc = Branch_MEM & Zero_MEM | Jump_MEM;
endmodule

module maindec(input  logic [6:0] op,
               output logic [1:0] ResultSrc,
               output logic       MemWrite,
               output logic       Branch, ALUSrc,
               output logic       RegWrite, Jump,
               output logic [1:0] ImmSrc,
               output logic [1:0] ALUOp);

  logic [10:0] controls;

  assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
          ResultSrc, Branch, ALUOp, Jump} = controls;

  always_comb
    case(op)
    // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
      7'b0000011: controls = 11'b1_00_1_0_01_0_00_0; // lw
      7'b0100011: controls = 11'b0_01_1_1_00_0_00_0; // sw
      7'b0110011: controls = 11'b1_xx_0_0_00_0_10_0; // R-type 
      7'b1100011: controls = 11'b0_10_0_0_00_1_01_0; // beq
      7'b0010011: controls = 11'b1_00_1_0_00_0_10_0; // I-type ALU
      7'b1101111: controls = 11'b1_11_0_0_10_0_00_1; // jal
      default:    controls = 11'bx_xx_x_x_xx_0_xx_0; // non-implemented instruction
    endcase
endmodule

module aludec(input  logic       opb5,
              input  logic [2:0] funct3,
              input  logic       funct7b5, 
              input  logic [1:0] ALUOp,
              output logic [2:0] ALUControl);

  logic  RtypeSub;
  assign RtypeSub = funct7b5 & opb5;  // TRUE for R-type subtract instruction

  always_comb
    case(ALUOp)
      2'b00:                ALUControl = 3'b000; // addition
      2'b01:                ALUControl = 3'b001; // subtraction
      default: case(funct3) // R-type or I-type ALU
                 3'b000:  if (RtypeSub) 
                            ALUControl = 3'b001; // sub
                          else          
                            ALUControl = 3'b000; // add, addi
                 3'b010:    ALUControl = 3'b101; // slt, slti
                 3'b110:    ALUControl = 3'b011; // or, ori
                 3'b111:    ALUControl = 3'b010; // and, andi
                 default:   ALUControl = 3'bxxx; // ???
               endcase
    endcase
endmodule

module datapath(input  logic        clk, reset,
                input  logic [1:0]  ResultSrc,  // MemToReg
                input  logic        PCSrc, ALUSrc,
                input  logic        RegWrite,
                input  logic [1:0]  ImmSrc,
                input  logic [2:0]  ALUControl,
                output logic        Zero_MEM,
                output logic [31:0] PC,
                input  logic [31:0] Instr,
                output logic [31:0] Instr_ID,
                output logic [31:0] ALUResult_MEM, WriteData_MEM,
                input  logic [31:0] ReadData,
                
                input logic         Branch,
                input logic         Jump,
                input logic         MemWrite,           

                output logic        Branch_MEM,
                output logic        Jump_MEM,
                output logic        MemWrite_MEM

                );

  logic [31:0] PCNext, PCPlus4, PCTarget, PCTarget_MEM;
  logic [31:0] PC_ID, PCPlus4_ID, PC_EX, PCPlus4_EX, PCPlus4_MEM, PCPlus4_WB;
  logic [31:0] ImmExt, ImmExt_EX;
  logic [31:0] SrcA, SrcB, WriteData, ReadData1_EX, WriteData_EX;
  logic [31:0] SrcA_final, SrcB_final;
  logic [1:0] UlaA, UlaB;
  logic [31:0] Result, ReadData_WB;
  logic [31:0] ALUResult_WB, ALUResult;

  logic [2:0]  ALUControl_EX;
  logic [1:0]  ResultSrc_EX, ResultSrc_MEM, ResultSrc_WB;

  logic [4:0]  Rd_EX, Rs1_EX, Rs2_EX;
  logic [4:0]  Rd_MEM, Rd_WB;

  logic Zero, ALUSrc_EX, MemWrite_EX, MemRead_EX, Branch_EX, RegWrite_EX, Jump_EX;
  logic MemRead_MEM, RegWrite_MEM, RegWrite_WB;

  // next PC logic
  flopr #(32) pcreg(clk, reset, enable_pc, PCNext, PC); 
  adder       pcadd4(PC, 32'd4, PCPlus4);
  adder       pcaddbranch(PC_EX, ImmExt_EX, PCTarget);
  mux2 #(32)  pcmux(PCPlus4, PCTarget_MEM, PCSrc, PCNext);
 
  // register file logic
  regfile     rf(clk, RegWrite_WB, Instr_ID[19:15], Instr_ID[24:20], 
                 Rd_WB, Result, SrcA, WriteData);
  extend      ext(Instr_ID[31:7], ImmSrc, ImmExt);

  forwardingunit forwardingunit(
      .Rs1_IDEX(Rs1_EX),
      .Rs2_IDEX(Rs2_EX),
      .Rd_EXMEM(Rd_MEM),
      .Rd_MEMWB(Rd_WB),
      .RegWrite_EXMEM(RegWrite_MEM),
      .RegWrite_MEMWB(RegWrite_WB),
      .UlaA(UlaA),
      .UlaB(UlaB)
  );

  hazarddetectionunit hazardunit(
      .MemRead_IDEX(MemRead_EX),
      .PCSrc(PCSrc),
      .Rd_IDEX(Rd_EX),
      .Rs1_IFID(Instr_ID[19:15]),
      .Rs2_IFID(Instr_ID[24:20]),
      .PCWrite(enable_pc),
      .IFIDWrite(enable_ifid),
      .IFIDFlush(flush_id),
      .IDEXFlush(flush_exec)
  );

  // ALU logic
  mux3 #(32)  srcaforwardingmux(ReadData1_EX, Result, ALUResult_MEM, UlaA, SrcA_final);
  mux3 #(32)  srcbforwardingmux(WriteData_EX, Result, ALUResult_MEM, UlaB, SrcB_final);
  
  mux2 #(32)  srcbmux(SrcB_final, ImmExt_EX, ALUSrc_EX, SrcB);
  alu         alu(SrcA_final, SrcB, ALUControl_EX, ALUResult, Zero);
  mux3 #(32)  resultmux(ALUResult_WB, ReadData_WB, PCPlus4_WB, ResultSrc_WB, Result);

  // pipeline registers
  IFID        ifid(clk, reset, enable_ifid, flush_id, PC, Instr, PCPlus4, PC_ID, Instr_ID, PCPlus4_ID);
  
  IDEX        idex(clk, reset, flush_exec,
                        PC_ID, SrcA, WriteData, ImmExt, PCPlus4_ID,          
                        Instr_ID[11:7], Instr_ID[19:15], Instr_ID[24:20],
                        
                        ALUControl,
                        ResultSrc, 
                        ALUSrc, MemWrite, ResultSrc == 2'b01, Branch, RegWrite, Jump,

                        ALUControl_EX,
                        ResultSrc_EX,
                        ALUSrc_EX, MemWrite_EX, MemRead_EX, Branch_EX, RegWrite_EX, Jump_EX,

                        PC_EX, ReadData1_EX, WriteData_EX, ImmExt_EX, PCPlus4_EX,
                        Rd_EX, Rs1_EX, Rs2_EX);

  EXMEM       exmem(clk, reset,
                        Zero,
                        ALUResult, SrcB_final, PCTarget, PCPlus4_EX,
                        Rd_EX,

                        ResultSrc_EX,
                        MemWrite_EX, MemRead_EX, Branch_EX, RegWrite_EX, Jump_EX,

                        ResultSrc_MEM,
                        MemWrite_MEM, MemRead_MEM, Branch_MEM, RegWrite_MEM, Jump_MEM,

                        Zero_MEM,
                        ALUResult_MEM, WriteData_MEM, PCTarget_MEM, PCPlus4_MEM,
                        Rd_MEM);
                        
  MEMWB       memwb(clk, reset,
                        ReadData, ALUResult_MEM, PCPlus4_MEM,
                        Rd_MEM,

                        ResultSrc_MEM, 
                        RegWrite_MEM,

                        ResultSrc_WB,
                        RegWrite_WB,

                        ReadData_WB, ALUResult_WB, PCPlus4_WB,
                        Rd_WB);

endmodule

module regfile(input  logic        clk, 
               input  logic        we3, 
               input  logic [ 4:0] a1, a2, a3, 
               input  logic [31:0] wd3, 
               output logic [31:0] rd1, rd2);

  logic [31:0] rf[31:0];

  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0

  always_ff @(posedge clk or negedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
  

endmodule

module adder(input  [31:0] a, b,
             output [31:0] y);

  assign y = a + b;
endmodule

module extend(input  logic [31:7] instr,
              input  logic [1:0]  immsrc,
              output logic [31:0] immext);
 
  always_comb
    case(immsrc) 
               // I-type 
      2'b00:   immext = {{20{instr[31]}}, instr[31:20]};  
               // S-type (stores)
      2'b01:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]}; 
               // B-type (branches)
      2'b10:   immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0}; 
               // J-type (jal)
      2'b11:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0}; 
      default: immext = 32'bx; // undefined
    endcase             
endmodule

module flopr #(parameter WIDTH = 8)
              (input  logic             clk, reset, enable,
               input  logic [WIDTH-1:0] d, 
               output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else if (enable) q <= d;
    else q <= q;
endmodule

module mux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

module imem(input  logic [31:0] a,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  initial
      $readmemh("riscvtest.txt",RAM);

  assign rd = RAM[a[31:2]]; // word aligned
endmodule

module dmem(input  logic        clk, we,
            input  logic [31:0] a, wd,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  assign rd = RAM[a[31:2]]; // word aligned

  always_ff @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule

module alu(input  logic [31:0] a, b,
           input  logic [2:0]  alucontrol,
           output logic [31:0] result,
           output logic        zero);

  logic [31:0] condinvb, sum;
  logic        v;              // overflow
  logic        isAddSub;       // true when is add or subtract operation

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];
  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] & alucontrol[0];

  always_comb
    case (alucontrol)
      3'b000:  result = sum;         // add
      3'b001:  result = sum;         // subtract
      3'b010:  result = a & b;       // and
      3'b011:  result = a | b;       // or
      3'b100:  result = a ^ b;       // xor
      3'b101:  result = sum[31] ^ v; // slt
      3'b110:  result = a << b[4:0]; // sll
      3'b111:  result = a >> b[4:0]; // srl
      default: result = 32'bx;
    endcase

  assign zero = (result == 32'b0);
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
  
endmodule

module IFID (input logic clk, reset, enable, flush,
            input logic [31:0] PC_in, Instr_in, PCPlus4_in,
            // + coisas da hazard unit
            output logic [31:0] PC_out, Instr_out, PCPlus4_out);


  always_ff @(posedge clk, posedge reset, posedge flush)
    if (reset | flush) begin
      PC_out    <= 32'b0;
      PCPlus4_out <= 32'b0;
      Instr_out <= 32'b0;
    end else if (enable) begin
      PC_out    <= PC_in;
      PCPlus4_out <= PCPlus4_in;
      Instr_out <= Instr_in;
    end else begin
      PC_out    <= PC_out;
      PCPlus4_out <= PCPlus4_out;
      Instr_out <= Instr_out;
    end

endmodule

module IDEX (input logic clk, reset, flush,
            input logic [31:0] PC_in, ReadData1_in, ReadData2_in, ImmExt_in, PCPlus4_in,  
            input logic [4:0] Rd_in, Rs1_in, Rs2_in,

            input logic [2:0] ALUControl_in,
            input logic [1:0] MemToReg_in,
            input logic ALUSrc_in, MemWrite_in, MemRead_in, Branch_in, RegWrite_in, Jump_in,

            output logic [2:0] ALUControl_out,
            output logic [1:0] MemToReg_out,
            output logic ALUSrc_out, MemWrite_out, MemRead_out, Branch_out, RegWrite_out, Jump_out,

            output logic [31:0] PC_out, ReadData1_out, ReadData2_out, ImmExt_out, PCPlus4_out,  
            output logic [4:0] Rd_out, Rs1_out, Rs2_out
            
            );

  always_ff @(posedge clk, posedge reset, posedge flush)
    if (reset | flush) begin
      PC_out         <= 32'b0;
      ReadData1_out  <= 32'b0;
      ReadData2_out  <= 32'b0;
      ImmExt_out     <= 32'b0;
      ALUControl_out <= 3'b0;
      Rd_out         <= 5'b0;
      Rs1_out        <= 5'b0;
      Rs2_out        <= 5'b0;
      PCPlus4_out   <= 32'b0;

      ALUSrc_out     <= 1'b0;
      MemWrite_out   <= 1'b0;
      MemRead_out    <= 1'b0;
      Branch_out     <= 1'b0;
      MemToReg_out   <= 2'b00;
      RegWrite_out   <= 1'b0;  
      Jump_out       <= 1'b0;   
    end else begin
      PC_out         <= PC_in;
      ReadData1_out  <= ReadData1_in;
      ReadData2_out  <= ReadData2_in;
      ImmExt_out     <= ImmExt_in;
      ALUControl_out <= ALUControl_in;
      Rd_out         <= Rd_in;
      Rs1_out        <= Rs1_in;
      Rs2_out        <= Rs2_in;
      PCPlus4_out   <= PCPlus4_in;

      ALUSrc_out     <= ALUSrc_in;
      MemWrite_out   <= MemWrite_in;
      MemRead_out    <= MemRead_in;
      Branch_out     <= Branch_in;
      MemToReg_out   <= MemToReg_in;
      RegWrite_out   <= RegWrite_in;
      Jump_out       <= Jump_in;
    end
endmodule

module EXMEM (input logic clk, reset,
              input logic        Zero_in,
              input logic [31:0] ALUResult_in, WriteData_in, AddPC_in, PCPlus4_in,
              input logic [4:0]  Rd_in,
 
              input logic [1:0] MemToReg_in,
              input logic MemWrite_in, MemRead_in, Branch_in, RegWrite_in, Jump_in,

              output logic [1:0] MemToReg_out,
              output logic MemWrite_out, MemRead_out, Branch_out, RegWrite_out, Jump_out,

              output logic       Zero_out,
              output logic [31:0] ALUResult_out, WriteData_out, AddPC_out, PCPlus4_out,
              output logic [4:0]  Rd_out);

  always_ff @(posedge clk, posedge reset)
    if (reset) begin
      Zero_out        <= 1'b0;
      ALUResult_out   <= 32'b0;
      WriteData_out   <= 32'b0;
      AddPC_out       <= 32'b0;
      Rd_out          <= 5'b0;
      PCPlus4_out     <= 32'b0;

      MemWrite_out    <= 1'b0;
      MemRead_out     <= 1'b0;
      Branch_out      <= 1'b0;
      MemToReg_out    <= 2'b00;
      RegWrite_out    <= 1'b0;
      Jump_out        <= 1'b0;
    end else begin
      Zero_out        <= Zero_in;
      ALUResult_out   <= ALUResult_in;
      WriteData_out   <= WriteData_in;
      AddPC_out       <= AddPC_in;
      Rd_out          <= Rd_in;
      PCPlus4_out     <= PCPlus4_in;

      MemWrite_out    <= MemWrite_in;
      MemRead_out     <= MemRead_in;
      Branch_out      <= Branch_in;
      MemToReg_out    <= MemToReg_in;
      RegWrite_out    <= RegWrite_in;
      Jump_out        <= Jump_in; 
    end
endmodule

module MEMWB (input logic clk, reset,
              input logic [31:0] ReadData_in, ALUResult_in, PCPlus4_in,
              input logic [4:0]  Rd_in,

              input logic [1:0] MemToReg_in,
              input logic RegWrite_in,

              output logic [1:0] MemToReg_out,
              output logic RegWrite_out,

              output logic [31:0] ReadData_out, ALUResult_out, PCPlus4_out,
              output logic [4:0]  Rd_out);

  always_ff @(posedge clk, posedge reset)
    if (reset) begin
      ReadData_out    <= 32'b0;
      ALUResult_out   <= 32'b0;
      Rd_out          <= 5'b0;
      PCPlus4_out     <= 32'b0;

      MemToReg_out    <= 2'b00;
      RegWrite_out    <= 1'b0;
    end else begin
      ReadData_out    <= ReadData_in;
      ALUResult_out   <= ALUResult_in;
      Rd_out          <= Rd_in;
      PCPlus4_out     <= PCPlus4_in;

      MemToReg_out    <= MemToReg_in;
      RegWrite_out    <= RegWrite_in;
    end
endmodule

module forwardingunit(
    input logic [4:0] Rs1_IDEX, Rs2_IDEX,
    input logic [4:0] Rd_EXMEM, Rd_MEMWB,
    input logic RegWrite_EXMEM, RegWrite_MEMWB,
    output logic [1:0] UlaA, UlaB
);

    always_comb begin
        UlaA = 2'b00;
        UlaB = 2'b00;

        if (RegWrite_EXMEM && (Rd_EXMEM != 0) && (Rd_EXMEM == Rs1_IDEX)) begin
            UlaA = 2'b10;
        end else if (RegWrite_MEMWB && (Rd_MEMWB != 0) && (Rd_MEMWB == Rs1_IDEX)) begin
            UlaA = 2'b01;
        end

        if (RegWrite_EXMEM && (Rd_EXMEM != 0) && (Rd_EXMEM == Rs2_IDEX)) begin
            UlaB = 2'b10;
        end else if (RegWrite_MEMWB && (Rd_MEMWB != 0) && (Rd_MEMWB == Rs2_IDEX)) begin
            UlaB = 2'b01;
        end
    end
endmodule

module hazarddetectionunit(
    input logic MemRead_IDEX,
    input logic PCSrc,
    input logic [4:0] Rd_IDEX,
    input logic [4:0] Rs1_IFID, Rs2_IFID,
    output logic PCWrite,
    output logic IFIDWrite,
    output logic IFIDFlush,
    output logic IDEXFlush
);
    
    always_comb begin
        PCWrite = 1'b1;
        IFIDWrite = 1'b1;
        IFIDFlush = 1'b0;
        IDEXFlush = 1'b0;

        if (MemRead_IDEX && ((Rd_IDEX == Rs1_IFID) || (Rd_IDEX == Rs2_IFID))) begin
            PCWrite = 1'b0;
            IFIDWrite = 1'b0;
        end

        if (PCSrc) begin
            IFIDFlush = 1'b1;
            IDEXFlush = 1'b1;
        end
    end
endmodule