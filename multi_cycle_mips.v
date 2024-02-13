
`timescale 1ns/100ps

   `define ADD  4'b0000
   `define SUB  4'b0001
   `define SLT  4'b0010
   `define SLTU 4'b0011
   `define AND  4'b0100
   `define XOR  4'b0101
   `define OR   4'b0110
   `define NOR  4'b0111
   `define LUI  4'b1000


module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE;
   reg [31:0] A, B, PC, IR, MDR, MAR;

   // Data Path Control Lines, donot forget, regs are not always regs !!
   reg setMRE, clrMRE, setMWE, clrMWE;
   reg Awrt, Bwrt, PCwrt , RFwrt,IRwrt, MDRwrt, MARwrt;
   reg [1:0] newPCsel; //mux controller to PC
   reg newPC; // for determine the next PC 
   reg [31:0] jumpPC ; 

   // Memory Ports Binding
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Mux & ALU Control Lines
   reg [2:0] aluOp;
   reg [1:0] aluSelB;
   reg SgnExt, aluSelA, MemtoReg, RegDst, IorD;


   // Wiring
   wire aluZero;
   wire [31:0] aluResult, rfRD1, rfRD2;


   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt)
         PC <= #0.1 newPC;

      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 IorD ? aluResult : PC;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;

      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;
   end

   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

      .WR( RegDst ? IR[15:11] : IR[20:16] ),
      .WD( MemtoReg ? MDR : aluResult )
   );

   // Sign/Zero Extension
   wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]} ;
   wire [27:0] jumpImm = {IR[25:0] , 2'b00};

   // ALU-A Mux
   wire [31:0] aluA = aluSelA ? A : PC;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)
   case (aluSelB)
      2'b00: aluB = B;
      2'b01: aluB = 32'h4;
      2'b10: aluB = SZout;
      2'b11: aluB = SZout << 2;
   endcase
   case (newPCsel)
      2'b00 : newPC = aluResult;
      2'b01 : newPC = jumpPC;
      2'b10 : newPC = A ;
   endcase

   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),

      .X( aluResult ),
      .Z( aluZero )
   );


   // Controller Starts Here

   // Controller State Registers
   reg [4:0] state, nxt_state;

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
      EX_ALU_R = 7, EX_ALU_I = 8,
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
      EX_BRA_1 = 25, EX_BRA_2 = 26;
      EXX_J_1 = 27;

   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD = 0;
         setMRE = 1;
         MARwrt = 1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;

      SgnExt = 'bx; IorD = 'bx;
      MemtoReg = 'bx; RegDst = 'bx;
      aluSelA = 'bx; aluSelB = 'bx; aluOp = 'bx;


      PCwrt = 0; newPCsel = 'bx
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;

      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            newPCsel = 2'b00;
            clrMRE = 1;
            aluSelA = 0;
            aluSelB = 2'b01;
            aluOp = `ADD;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000_000:             // R-format
                  case( IR[5:3] )
                     3'b000: ;
                     3'b001: //jr and jalr

                        case(IR[2:0])
                           3'b000 : 
                              PCwrt = 1;
                              newPCsel = 2'b10 ;
                              nxt_state = EXX_J_1;
                        endcase
                      
                     3'b010: ;
                     3'b011: ;
                     3'b100: nxt_state = EX_ALU_R;
                     3'b101: nxt_state = EX_ALU_R;
                     3'b110: ;
                     3'b111: ;
                  endcase

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_110,             // xori
               6'b001_111:             // lui
                  nxt_state = EX_ALU_I;

               6'b100_011:
                  nxt_state = EX_LW_1;

               6'b101_011:
                  nxt_state = EX_SW_1;

               6'b000_100,
               6'b000_101:
                  nxt_state = EX_BRA_1;


               //for jump 
               6'b000_010: 
                  jumpPC = {PC[31:28] , jumpImm};
                  PCwrt = 1;
                  newPCsel = 2'b01;
                  nxt_state = EXX_J_1;
                  
                  

               // rest of instructiones should be decoded here

            endcase
         end

         EXX_J_1 : begin
            PrepareFetch
         end

         EX_ALU_R: begin
            RegDst = 1
            RFwrt = 1 
            MemtoReg = 0;
            aluSelA = 1 ;
            aluSelB = 2'b00;
            case(IR[5:0])

               6'b100000, //add
               6'b100001 : //addu
                  aluOp = `ADD;                 
                  PrepareFetch;

               6'b100010, //sub
               6'b100011 : //subu
                  aluOp = `SUB;
                  PrepareFetch

               6'b100100: //and
                  aluOp = `AND;
                  PrepareFetch

               6'b100101: //or
                  aluOp = `OR;
                  PrepareFetch

               6'b100110: //xor
                  aluOp = `XOR;
                  PrepareFetch

               6'b100111: //nor
                  aluOp = `NOR;
                  PrepareFetch

               6'b101010: //slt
                  aluOp = `SLT;
                  PrepareFetch

               6'b101011: //sltu
                  aluOp = `SLTU;
                  PrepareFetch
            endcase
         end

         EX_ALU_I: begin
            RegDst = 0 ;
            MemtoReg = 0 ;
            RFwrt = 1;
            aluSelA = 1 ;
            aluSelB = 2'b10;

            case(IR[31:26]) 
               6'b001_000 :            // addi
                  SgnExt = 1;
                  aluOp = `ADD;                 
                  PrepareFetch;
                  
               6'b001_001:             // addiu
                  SgnExt = 1;
                  aluOp = `ADD;                 
                  PrepareFetch;
                  
               6'b001_010:             // slti
                  SgnExt = 1;
                  aluOp = `SLT;                 
                  PrepareFetch;

               6'b001_011:             // sltiu
                  SgnExt = 1;
                  aluOp = `SLTU;                 
                  PrepareFetch;

               6'b001_100:             // andi
                  SgnExt = 0;
                  aluOp = `AND;                 
                  PrepareFetch;

               6'b001_101:             // ori
                  SgnExt = 0;
                  aluOp = `OR;                 
                  PrepareFetch;

               6'b001_110:             // xori
                  SgnExt = 0;
                  aluOp = `XOR;  
                  PrepareFetch;

               6'b001_111:             // xori
                  SgnExt = 0;
                  aluOp = `LUI;  
                  PrepareFetch;
            endcase
         end

         EX_LW_1: begin
            setMRE = 1;
            MARwrt = 1;
            IorD = 1;
            SgnExt = 1;
            aluSelA = 1;
            aluSelB = 2'b10;
            aluOp = `ADD;
            nxt_state = EX_LW_2;
         end

         EX_LW_2: begin
            nxt_state = EX_LW_3;
         end

         EX_LW_3: begin
            nxt_state = EX_LW_4;
         end

         EX_LW_4: begin
            clrMRE = 1;
            MDRwrt = 1;
            nxt_state = EX_LW_5;
         end

         EX_LW_5: begin
            RegDst = 0 ;
            MemtoReg = 1;
            RFwrt = 1;
            PrepareFetch;
         end


         EX_SW_1: begin
            setMWE = 1;
            MARwrt = 1;
            IorD = 1;
            SgnExt = 1;
            aluSelA = 1;
            aluSelB = 2'b10;
            aluOp = `ADD;
            nxt_state = EX_SW_2;
         end

         EX_SW_2: begin     
            clrMWE = 1;       
            nxt_state = EX_SW_3;
         end

         EX_SW_3: begin     
            PrepareFetch;
         end         

         EX_BRA_1: begin
            aluSelA = 1 ;
            aluSelB = 2'b00;
            aluOp = `SUB;
            case (IR[31:26])
               6'b00_100:
                  if (aluZero) nxt_state = EX_BRA_2;
                  else PrepareFetch;
               6'b000_101:
                  if (aluZero) PrepareFetch;
                  else nxt_state = EX_BRA_2;
            endcase
         end

         EX_BRA_2: begin
            //for sum
            aluSelA = 0 ;
            aluSelB = 2'b11;
            SgnExt = 1;
            aluOp = `ADD;
            //for memory
            setMRE = 1;
            MARwrt = 1;
            IorD = 1;
            PCwrt = 1;
            newPCsel = 2'b00;
            nxt_state = FETCH1;

         end

            . . . . .
            . . . . .
            . . . . .

      endcase

   end

endmodule

//==============================================================================

module my_alu(
   input [2:0] Op,
   input [31:0] A,
   input [31:0] B,

   output [31:0] X,
   output        Z
);

   wire sub = Op != `ADD;

   wire [31:0] bb = sub ? ~B : B;

   wire [32:0] sum = A + bb + sub;

   wire sltu = ! sum[32];

   wire v = sub ? 
        ( A[31] != B[31] && A[31] != sum[31] )
      : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         `LUI : x = {B[15:0], 16'h0};
         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule

//==============================================================================
