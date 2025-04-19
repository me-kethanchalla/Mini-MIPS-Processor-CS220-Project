timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 04/07/2025 02:43:38 PM
// Design Name: 
// Module Name: alu
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////






module sign_ext(
    input  [15:0] in,
    output [31:0] out);


  assign out = {{16{in[15]}}, in};
endmodule
    


module mux2 #(parameter WIDTH = 32)(
  input  [WIDTH-1:0] d0,
  input  [WIDTH-1:0] d1,
  input             sel,
  output [WIDTH-1:0] y
);
  assign y = sel ? d1 : d0;
endmodule



module mult_hi_lo(
  input            clk,
  input            rst,
  input            start,
  input            is_signed,
  input  [31:0]    a,
  input  [31:0]    b,
  output reg [31:0] hi,
  output reg [31:0] lo
);
  wire signed [63:0] prod_signed  = $signed(a) * $signed(b);
  wire        [63:0] prod_unsigned = a * b;
  wire [63:0] result = is_signed ? prod_signed : prod_unsigned;

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      hi <= 0;
      lo <= 0;
    end else if (start) begin
      hi <= result[63:32];
      lo <= result[31: 0];
    end
  end
endmodule

module alu ( a1, a2, ctrl, out, zero );
input [31:0] a1, a2;
input [5:0] ctrl;
output reg [31:0] out;
output reg zero;

wire [31:0] B_out;
wire[31:0] adder_out;
wire eq, lt, gt, ge, le;
fp_comparator comp(a1, a2, eq, lt, gt, le, ge);
fp_add_or_sum op(a2, ctrl, B_out);
fp_adder adder(a1, B_out, adder_out);

always @(*) begin
    zero = (out == 0);  
end

always@(*) begin
    case (ctrl) 
    // for now all unsigned operations have been ignored
    
        //arithmetic and logical 
        
        6'd0: out <= a1+a2;
        6'd1: out <= a1-a2;
        6'd2: out <= $unsigned(a1) + $unsigned(a2);
        6'd3: out <= $unsigned(a1) - $unsigned(a2);
        6'd4: out <= a1+a2;
        6'd5: out <= $unsigned(a1) + $unsigned(a2);
        
        
        6'd6: out <= a1 * a2;  //madd
        6'd7: out <= a1 * a2;  //maddu
        6'd8: out <= a1-a2; //mult

        //logical
        6'd9: out <= a1&a2; 
        6'd10: out <= a1|a2;
        6'd11: out <= a1&a2; 
        6'd12: out <= a1|a2;
        
        6'd13: out <= a1^1; //this is 'not' ; haha 
        6'd14: out <= a1^a2;
        
        //shift logical
        6'd15: out <= a1 << a2[10:6];
        6'd16: out <= a1 >> a2[10:6];
        6'd17: out <= a1 <<< a2[10:6];
        6'd18: out <= a1 >>> a2[10:6];
        
        
        //data transfer
        6'd19: out <= a1 + (a2<<2); 
        6'd20: out <= a1 + (a2<<2); 
        6'd21: begin 
            out <= a1;
            out[31:16] <= a2;
            end          

        //branching
        6'd22: zero <= (a1==a2) ? 1'd1:1'd0;
        6'd23: zero <= (a1!=a2) ? 1'd1:1'd0;
        6'd24: zero <= (a1>a2) ? 1'd1:1'd0;
        6'd25: zero <= (a1>=a2) ? 1'd1:1'd0;
        6'd26: zero <= (a1<a2) ? 1'd1:1'd0;
        6'd27: zero <= (a1<=a2) ? 1'd1:1'd0;
        6'd28: zero <= ($unsigned(a1)<$unsigned(a2)) ? 1'd1:1'd0;
        6'd29: zero <= ($unsigned(a1)>$unsigned(a2)) ? 1'd1:1'd0;
        
        //jump
        //no need of any implementation in the ALU, but for consistent notation, skipping 3 numbers here.
        
        
        //comparision
        6'd33: out <= (a1 < a2) ? 1:0;
        6'd34: out <= (a1 < a2) ? 1:0; 
        6'd35: out <= (a1 == a2) ? 1:0; 
        
        //floating point 
        6'd36: out <= a1; //mfcl
        6'd37: out <= a1; //mtcl
        6'd38: out <= adder_out; //add.s
        6'd39: out <= adder_out; //sub.s
        6'd40: out <= eq;  //cc.eq
        6'd41: out <= le;
        6'd42: out <= lt;
        6'd43: out <= ge;
        6'd44: out <= gt;
        6'd45: out <= a1;
        default : out <= 32'd0;
    endcase
end
endmodule



module alu_ctrl( alu_op,alu_data, alu_branch,alu_imm, funct, fp_instr, fp_1, fp_2, alu_ctrl) ;
    input [1:0] alu_op;
    input [2:0] alu_branch;
    input [1:0] alu_data;
    input [2:0] alu_imm;
    input [5:0] funct;
    input [2:0] fp_instr;
    input  fp_1, fp_2;
    output reg [5:0] alu_ctrl;
    
    always@(*) begin
    if(fp_instr == 3'd0) begin
    case (alu_op)
    
    
        2'd0 : begin
            case(alu_data) 
                2'd0 : alu_ctrl <= 6'd19;
                2'd1 : alu_ctrl <= 6'd20;
                2'd2 : alu_ctrl <= 6'd21;
                2'd3 : begin
                if (fp_1 == 1 && fp_2==0) alu_ctrl <= 6'd36;
                else if (fp_1 == 0 && fp_2 == 0) alu_ctrl <= 6'd37;
                else if (fp_1 == 1 && fp_2 == 1) alu_ctrl <= 6'd45;
                end               
            endcase  
        end   
             
        2'd1 : begin
            case(alu_branch) 
                3'd0 : alu_ctrl <= 6'd22;
                3'd1 : alu_ctrl <= 6'd23;
                3'd2 : alu_ctrl <= 6'd24;
                3'd3 : alu_ctrl <= 6'd25;
                3'd4 : alu_ctrl <= 6'd26;
                3'd5 : alu_ctrl <= 6'd27;
                3'd6 : alu_ctrl <= 6'd28;
                3'd7 : alu_ctrl <= 6'd29; 
                
            endcase 
        end        
        
        2'd2 : begin
            case(funct) 
                6'd0  : alu_ctrl <= 6'd0;
                6'd1  : alu_ctrl <= 6'd1;
                6'd2  : alu_ctrl <= 6'd2;
                6'd3  : alu_ctrl <= 6'd3;
                // 4, 5 are immediates addi, addiu
                6'd6  : alu_ctrl <= 6'd6;
                6'd7  : alu_ctrl <= 6'd7;
                6'd8  : alu_ctrl <= 6'd8;
                6'd9  : alu_ctrl <= 6'd9;
                6'd10 : alu_ctrl <= 6'd10;
                // 11, 12 are immediates andi, ori
                6'd13 : alu_ctrl <= 6'd13;
                // 14 is immediate xori
                6'd15 : alu_ctrl <= 6'd15;
                6'd16 : alu_ctrl <= 6'd16;
                6'd17 : alu_ctrl <= 6'd17;
                6'd18 : alu_ctrl <= 6'd18;
                6'd33 : alu_ctrl <= 6'd33;
                // 34, 35 are immediates slti, seq  
                
            endcase 
            end
            
        2'd3 : begin
            case(alu_imm) 

                // 4, 5 are immediates addi, addiu
                3'd0  : alu_ctrl <= 6'd4;
                3'd1  : alu_ctrl <= 6'd5;
                
                // 11, 12 are immediates andi, ori
                3'd2  : alu_ctrl <= 6'd11;
                3'd3  : alu_ctrl <= 6'd12;
                
                // 14 is immediate xori
                3'd4 : alu_ctrl <= 6'd14; 
                          
                // 34, 35 are immediates slti, seq 
                3'd5 : alu_ctrl <= 6'd34;
                3'd6 : alu_ctrl <= 6'd35;
   
            endcase       
        end 
    
    endcase
    end
    
    else if(fp_instr!=0) begin
    case (fp_instr) 
       
        3'd1: alu_ctrl <= 38;
        3'd2: alu_ctrl <= 39;
        3'd3: alu_ctrl <= 40;
        3'd4: alu_ctrl <= 41;
        3'd5: alu_ctrl <= 42;
        3'd6: alu_ctrl <= 43;
        3'd7: alu_ctrl <= 44;
    
    endcase 
    
    end
    end
    
    
endmodule


module ctrl (opcode, mem_write, reg_write, alu_op,alu_data, alu_branch ,alu_imm,
mux_alu_src, mux_reg_write_addr, mux_reg_write_data, mux_jump , branch, fp_instr, fp_1, fp_2) ;

input [5:0] opcode;
output reg mem_write, reg_write;
output reg [1:0] alu_op;
output reg[2:0] alu_branch;
output reg[1:0] alu_data;
output reg[2:0] alu_imm;
output reg mux_alu_src, mux_reg_write_addr, mux_reg_write_data,mux_jump , branch;
output reg [2:0] fp_instr;
output reg fp_1, fp_2;

always@(*) begin
    
    case(opcode)
        
        //rtype
        6'd0 : begin
        
            alu_op <= 2'd2;
            mem_write <= 0;
            reg_write <= 1;
            alu_data <= 2'd0;
            alu_branch <= 3'd0;
            alu_imm <= 3'd0;
            mux_alu_src <= 0;
            mux_reg_write_addr <= 1;
            mux_reg_write_data <= 0;
            mux_jump <= 0;
            branch <= 0;
            fp_instr <=0;
            fp_1 <=0;
            fp_2 <=0;
            
        end
        
        //jump
        6'd1 : begin
            mem_write <= 0;
            reg_write <= 1;
            mux_jump <= 1;
            fp_instr <=0;
            fp_1 <=0;
            fp_2 <=0;
        
        end
        
        //branch
        6'd2, 6'd3, 6'd4, 6'd5, 6'd6, 6'd7, 6'd8, 6'd9 : begin
            
            alu_op <= 2'd1;
            mem_write <= 0;
            reg_write <= 0;
            alu_data <= 2'd0;
            alu_branch <= opcode - 6'd2; //this is variable in branch based on which type of branch
            alu_imm <= 3'd0;
            mux_reg_write_addr <= 0;
            mux_alu_src <= 1;
            mux_reg_write_data <= 0; //not used however
            mux_jump <= 0;
            branch <= 1;
            fp_instr <=0;
            fp_1 <=0;
            fp_2 <=0;
        end
        
        // load data
        6'd10 : begin
            alu_op <= 2'd0;
            mem_write <= 0;
            reg_write <= 1;
            alu_data <= 2'd0; //this is variable here
            alu_branch <= 3'd0;
            alu_imm <= 3'd0;
            mux_reg_write_addr <= 0;
            mux_alu_src <= 1;
            mux_reg_write_data <= 1;
            mux_jump <= 0;
            branch <= 0;
            fp_instr <= 0;
            fp_1 <= 0;
            fp_2 <= 0;
        end
        
        // store data
        6'd11 : begin
        
            alu_op <= 2'd0;
            mem_write <= 1;
            reg_write <= 0;
            alu_data <= 2'd1; //this is variable here
            alu_branch <= 3'd0;
            alu_imm <= 3'd0;
            mux_reg_write_addr <= 0;
            mux_alu_src <= 1;
            mux_reg_write_data <= 0; // not used
            mux_jump <= 0;
            branch <= 0;
            fp_instr <=0;
            fp_1 <=0;
            fp_2 <=0;
        end
        
        // load data immediate
        6'd12 : begin
            
            alu_op <= 2'd0;
            mem_write <= 0;
            reg_write <= 1;
            alu_data <= 2'd2; //this is variable here
            alu_branch <= 3'd0;
            alu_imm <= 3'd0;
            mux_reg_write_addr <= 0;
            mux_alu_src <= 1;
            mux_reg_write_data <= 1;
            mux_jump <= 0;
            branch <= 0;
            fp_instr <=0;
            fp_1 <=0;
            fp_2 <=0;
        end
        
        
        // immediates
        6'd13, 6'd14, 6'd15, 6'd16, 6'd17, 6'd18, 6'd19: begin
        
            alu_op <= 2'd3;
            mem_write <= 0;
            reg_write <= 1;
            alu_data <= 2'd0;
            alu_branch <= 3'd0;
            alu_imm <= opcode - 6'd13; // this is variable
            mux_reg_write_addr <= 0;
            mux_alu_src <= 1;
            mux_reg_write_data <= 0;
            mux_jump <= 0;
            branch <= 0;
            fp_instr <=0;
            fp_1 <=0;
            fp_2 <=0;
        end
        
        //mfcl
        6'd20: begin
        
            alu_op <= 2'd0;
            mem_write <= 0;
            reg_write <= 1;
            alu_data <= 2'd3;
            alu_branch <= 3'd0;
            alu_imm <= 3'd0; 
            mux_reg_write_addr <= 0;
            mux_alu_src <= 1; //we keep this as zero 
            mux_reg_write_data <= 0; 
            mux_jump <= 0;
            branch <= 0;
            fp_instr <=0;
            fp_1 <= 1 ; //the source is fp sincce we are moving fp into int
            fp_2 <= 0;  // the dest is int
        end
        
        //mtcl
        6'd21: begin
        
            alu_op <= 2'd0;
            mem_write <= 0;
            reg_write <= 1;
            alu_data <= 2'd3;
            alu_branch <= 3'd0;
            alu_imm <= 3'd0; 
            mux_reg_write_addr <= 0;
            mux_alu_src <= 1; //we keep this as zero 
            mux_reg_write_data <= 0; 
            mux_jump <= 0;
            branch <= 0;
            fp_instr <=0;
            fp_1 <= 0 ; //the source is fp sincce we are moving fp into int
            fp_2 <= 1;  // the dest is int
        end
        

        
//      add.s
        6'd22: begin 
            
            alu_op <= 2'd2;
            mem_write <= 0;
            reg_write <= 1;
            alu_data <= 2'd0;
            alu_branch <= 3'd0;
            alu_imm <= 3'd0;
            mux_alu_src <= 0;
            mux_reg_write_addr <= 1;
            mux_reg_write_data <= 0;
            mux_jump <= 0;
            branch <= 0;
            fp_instr <= 1;
            fp_1 <=1;
            fp_2 <=1;
           
        end 
        
//      sub.s
        6'd23: begin 
            
            alu_op <= 2'd2;
            mem_write <= 0;
            reg_write <= 1;
            alu_data <= 2'd0;
            alu_branch <= 3'd0;
            alu_imm <= 3'd0;
            mux_alu_src <= 0;
            mux_reg_write_addr <= 1;
            mux_reg_write_data <= 0;
            mux_jump <= 0;
            branch <= 0;
            fp_instr <= 2;
            fp_1 <=1;
            fp_2 <=1;
        end    

//      5 comparative options for floating point
        6'd24, 6'd25, 6'd26, 6'd27, 6'd28: begin 
            
            alu_op <= 2'd2;
            mem_write <= 0;
            reg_write <= 1;
            alu_data <= 2'd0;
            alu_branch <= 3'd0;
            alu_imm <= 3'd0;
            mux_alu_src <= 0;
            mux_reg_write_addr <= 1;
            mux_reg_write_data <= 0;
            mux_jump <= 0;
            branch <= 0;
            fp_instr <= opcode - 6'd21;
            fp_1 <=1;
            fp_2 <=1;
        end   
        
        //mov.s
        //this is same as mfcl, mtcl
        6'd29: begin
        
            alu_op <= 2'd0;
            mem_write <= 0;
            reg_write <= 1;
            alu_data <= 2'd3;
            alu_branch <= 3'd0;
            alu_imm <= 3'd0; 
            mux_reg_write_addr <= 0;
            mux_alu_src <= 1; //we keep this as zero 
            mux_reg_write_data <= 0; 
            mux_jump <= 0;
            branch <= 0;
            fp_instr <=0;
            fp_1 <= 1 ; //the source is fp 
            fp_2 <= 1;  // the dest is fp
        end
    endcase    
end
endmodule



module memory(
    input clk,
    input write_enable,
    input [31:0] read_address,
    input [31:0] write_address,
    input [31:0] data_in,
    output [31:0] data_out
);

    reg [31:0] mem [0:1023];

    always @(posedge clk) begin
        if (write_enable)
            mem[write_address] <= data_in;
    end
    assign data_out = mem[read_address];  // asynchronous read

endmodule



module PC (
    input  wire [31:0] in_addr,
    input  wire        mux_jump,
    input  wire [25:0] instruction,
    input  wire        branch,
    input  wire        alu_zero,
    input  wire [31:0] offset,
    output reg  [31:0] out_addr
);

  
    wire [31:0] addr_incr_by_4 = in_addr + 32'd4;
    wire        branch_taken   = branch && alu_zero;
    wire [27:0] jump_target    = {instruction, 2'b00};
    wire [31:0] jump_addr      = {addr_incr_by_4[31:28], jump_target};
    wire [31:0] branch_addr    = addr_incr_by_4 + (offset << 2);

    // Combinational logic
    always @(*) begin
        if (mux_jump)
            out_addr = jump_addr;
        else if (branch_taken)
            out_addr = branch_addr;
        else
            out_addr = addr_incr_by_4;
    end

endmodule



module register_file (clk,rst,we, fp_instr, fp_1, fp_2, read_address_1, read_address_2, write_address,
 write_data, read_data_1, read_data_2);
    input clk, rst , we;
    input [2:0] fp_instr;
    input fp_1, fp_2;
    input [31:0] read_address_1, read_address_2, write_address, write_data;
    output [31:0] read_data_1, read_data_2;

    reg [31:0] GPR[63:0];          //1st 32 registers are gpr next 32 are fpr      
    reg [31:0] FPR[63:0];  

    always @ (posedge clk) begin
        if(rst) begin
            GPR[0] <= 0;
            GPR[29] <= 200;         //assume stack pointer starts at 500
            
            FPR[13] <= 32'hc1d9f1aa;
            FPR[14] <= 32'h427d5d2f;

        end
        
        else begin
            if(we) begin
//                if(mul == 1) begin
//                    {GPR[26], GPR[27]} <=  {write_data_2, write_data_1};
//                end    

//                else if(mul == 2) begin
//                    // {hi, lo} <= {hi, lo} + {write_data_2, write_data_1};
//                    {GPR[26], GPR[27]} <= {GPR[26], GPR[27]} + {write_data_2, write_data_1};
//                end   
                
//                else begin 
                    case (fp_instr)
                    
                        3'd0 : begin
                            if(fp_2 == 0)                               
                                GPR[write_address] <= write_data;
                            else if (fp_2 == 1) 
                                FPR[write_address] <= write_data;
                        end
                        
                        3'd1, 3'd2, 3'd3, 3'd4, 3'd5, 3'd6, 3'd7 : begin
                            FPR[write_address] <= write_data;
                        end
                        
                        
                    endcase
//                end
            end     

        end
    end
    assign read_data_1 = fp_1 ? FPR[read_address_1] : GPR[read_address_1];
    assign read_data_2 = fp_1 ? FPR[read_address_2] : GPR[read_address_2];
    // assign read_data_2 = GPR_FPR[read_address_2];

endmodule

module fp_add_or_sum(B, ctrl, B_out);
   input [31:0] B;
   input [4:0] ctrl;

   output reg [31:0] B_out;

   always @ (*) begin
      if(ctrl == 39) B_out <= {~B[31], B[30:0]}; 
      else B_out <= B;

   end
endmodule

   
module fp_adder(
    input  [31:0] a,
    input  [31:0] b,
    output reg [31:0] sum
);

  reg         a_sign, b_sign;
  reg [7:0]   a_exp,  b_exp;
  reg [22:0]  a_frac, b_frac;
  reg [23:0]  a_mant, b_mant;

  reg         op1_sel;
  reg         op1_sign, op2_sign;
  reg [7:0]   exp_large;
  reg [23:0]  op1_mant, op2_mant;
  reg [7:0]   exp_diff;

  reg [27:0]  op1_ext, op2_ext;
  reg [27:0]  mant_sum;
  reg         result_sign;

  reg [27:0]  mant_norm;     // Normalized mantissa
  reg [7:0]   exp_result;    // Adjusted exponent after normalization
  integer i;
  integer found;           // Flag to indicate first '1' found
  integer shift;           // Number of positions to shift for normalization

  // Rounding signals
  reg [23:0]  mantissa_final; // 24-bit mantissa (1 implicit bit + 23 fraction bits)
  reg [2:0]   round_bits;     // Guard, round, and sticky bits

  // Main combinational block
  always @(*) begin
    // 1. Extract the fields of both operands.
    a_sign = a[31];
    b_sign = b[31];
    a_exp  = a[30:23];
    b_exp  = b[30:23];
    a_frac = a[22:0];
    b_frac = b[22:0];

    // For normalized numbers, the implicit MSB is 1.
    a_mant = (a_exp == 0) ? {1'b0, a_frac} : {1'b1, a_frac};
    b_mant = (b_exp == 0) ? {1'b0, b_frac} : {1'b1, b_frac};

    // 2. Determine which operand has the larger magnitude.
    if ((a_exp > b_exp) || ((a_exp == b_exp) && (a_mant >= b_mant))) begin
      op1_sel   = 1;        // A is larger
      op1_sign  = a_sign;
      op2_sign  = b_sign;
      exp_large = a_exp;
      op1_mant  = a_mant;
      op2_mant  = b_mant;
      exp_diff  = a_exp - b_exp;
    end
    else begin
      op1_sel   = 0;        // B is larger
      op1_sign  = b_sign;
      op2_sign  = a_sign;
      exp_large = b_exp;
      op1_mant  = b_mant;
      op2_mant  = a_mant;
      exp_diff  = b_exp - a_exp;
    end

    // 3. Align the mantissas.
    // Extend 24-bit mantissas to 28 bits: one extra MSB and 3 LSB guard bits.
    op1_ext = {1'b0, op1_mant, 3'b000};
    op2_ext = {1'b0, op2_mant, 3'b000} >> exp_diff;

    // 4. Perform addition or subtraction.
    if (op1_sign == op2_sign) begin
      mant_sum    = op1_ext + op2_ext;
      result_sign = op1_sign;  // Same sign: straightforward addition.
    end
    else begin
      // Subtraction: since op1 is the larger magnitude, subtract op2 from op1.
      mant_sum    = op1_ext - op2_ext;
      result_sign = op1_sign;
    end

    // 5. Normalize the result.
    if (mant_sum[27] == 1'b1) begin
      // If there's a carry-out, shift right by 1 and increment the exponent.
      mant_norm  = mant_sum >> 1;
      exp_result = exp_large + 1;
    end
    else begin
      if (mant_sum != 0) begin
        shift = 0;
        found = 0;        // Initialize the flag.
        mant_norm = mant_sum;
        // Find the position of the first '1' in bits [26:0]
        for (i = 26; i >= 0; i = i - 1) begin
          if (!found && mant_norm[i] == 1'b1) begin
            shift = 26 - i;
            found = 1;  // Mark that the first '1' has been found.
          end
        end
        mant_norm  = mant_norm << shift;
        exp_result = exp_large - shift;
      end
      else begin
        // If the result is zero.
        mant_norm  = 0;
        exp_result = 0;
      end
    end

    // 6. Rounding: use bits [26:3] for the 24-bit mantissa; bits [2:0] are for rounding.
    mantissa_final = mant_norm[26:3];
    round_bits     = mant_norm[2:0];

    // Round-to-nearest, ties-to-even.
    if ((round_bits > 3'b100) ||
        ((round_bits == 3'b100) && (mantissa_final[0] == 1'b1))) begin
      mantissa_final = mantissa_final + 1;
      // Handle rounding overflow (e.g., rounding causes a carry).
      if (mantissa_final == 24'h800000) begin
        mantissa_final = mantissa_final >> 1;
        exp_result = exp_result + 1;
      end
    end

    // 7. Pack the result into IEEE-754 format.
    // Drop the implicit bit: use lower 23 bits of mantissa_final.
    sum = {result_sign, exp_result, mantissa_final[22:0]};
  end

endmodule

module fp_comparator (
    input  [31:0] a,   // First floating-point number in IEEE-754 format
    input  [31:0] b,   // Second floating-point number in IEEE-754 format
    output        eq,  // '1' if a equals b
    output        lt,  // '1' if a is less than b
    output        gt,  // '1' if a is greater than b
    output        le,  // '1' if a is less than or equal to b
    output        ge   // '1' if a is greater than or equal to b
    );

  // Extract sign, exponent and fraction parts
  wire        a_sign, b_sign;
  wire [7:0]  a_exp, b_exp;
  wire [22:0] a_frac, b_frac;

  assign a_sign = a[31];
  assign b_sign = b[31];
  assign a_exp  = a[30:23];
  assign b_exp  = b[30:23];
  assign a_frac = a[22:0];
  assign b_frac = b[22:0];

  // Equality can be determined by simple bitwise comparison
  assign eq = (a == b);

  // Internal registers for less-than and greater-than results
  reg lt_int, gt_int;

  // Combinational block to compare 'a' and 'b'
  always @(*) begin
    // Default assignments for the flags
    lt_int = 1'b0;
    gt_int = 1'b0;

    // If the numbers are exactly equal, no further comparison is needed.
    if (a == b) begin
      lt_int = 1'b0;
      gt_int = 1'b0;
    end else begin
      // Compare the sign bits
      if (a_sign != b_sign) begin
        // If signs differ, the negative number is less
        lt_int = a_sign;
        gt_int = b_sign;
      end
      else begin
        // Both numbers have the same sign
        // For positive numbers, larger exponent or fraction means a larger number.
        if (a_sign == 1'b0) begin
          if (a_exp < b_exp)
            lt_int = 1'b1;
          else if (a_exp > b_exp)
            gt_int = 1'b1;
          else begin
            // Exponents are equal, compare fraction (mantissa)
            if (a_frac < b_frac)
              lt_int = 1'b1;
            else if (a_frac > b_frac)
              gt_int = 1'b1;
          end
        end
        // For negative numbers, the comparison is reversed
        else begin
          if (a_exp < b_exp)
            gt_int = 1'b1;
          else if (a_exp > b_exp)
            lt_int = 1'b1;
          else begin
            if (a_frac < b_frac)
              gt_int = 1'b1;
            else if (a_frac > b_frac)
              lt_int = 1'b1;
          end
        end
      end
    end
  end

  // Drive outputs from the internal registers and computed equality
  assign lt = lt_int;
  assign gt = gt_int;
  assign le = lt_int || eq; // a is less than or equal to b when it's less than or exactly equal to b
  assign ge = gt_int || eq; // a is greater than or equal to b when it's greater than or exactly equal to b

endmodule 




module single_cycle(
  input         clk,
  input         rst,
  output [31:0] pc_out
);
  // Program Counter wires
  wire [31:0] pc_in, pc_curr;
  wire        branch_taken;
  wire        alu_zero;

  // Instruction fields
  wire [31:0] instr;
  wire [5:0]  opcode = instr[31:26];
  wire [4:0]  rs     = instr[25:21];
  wire [4:0]  rt     = instr[20:16];
  wire [4:0]  rd     = instr[15:11];
  wire [15:0] imm    = instr[15:0];
  wire [25:0] addr   = instr[25:0];
  wire [5:0]  funct  = instr[5:0];

  // Control unit signals
  wire        mem_write, reg_write;
  wire [1:0]  alu_op;
  wire [2:0]  alu_branch;
  wire [1:0]  alu_data;
  wire [2:0]  alu_imm;
  wire        mux_alu_src, mux_reg_wr_addr;
  wire        mux_reg_wr_data, mux_jump;
  wire        branch;
  wire [2:0]  fp_instr;
  wire        fp_1, fp_2;

  ctrl ctl(
    .opcode(opcode),
    .mem_write(mem_write),
    .reg_write(reg_write),
    .alu_op(alu_op),
    .alu_data(alu_data),
    .alu_branch(alu_branch),
    .alu_imm(alu_imm),
    .mux_alu_src(mux_alu_src),
    .mux_reg_write_addr(mux_reg_wr_addr),
    .mux_reg_write_data(mux_reg_wr_data),
    .mux_jump(mux_jump),
    .branch(branch),
    .fp_instr(fp_instr),
    .fp_1(fp_1),
    .fp_2(fp_2)
  );

  // Instruction memory
  memory instr_mem(
    .clk(clk),
    .write_enable(1'b0),
    .read_address(pc_curr[11:2]),
    .write_address(32'b0),
    .data_in(32'b0),
    .data_out(instr)
  );

  // Register file
  wire [31:0] read_data1, read_data2;
  register_file rf(
    .clk(clk), .rst(rst), .we(reg_write),
    .fp_instr(fp_instr), .fp_1(fp_1), .fp_2(fp_2),
    .read_address_1(rs), .read_address_2(rt),
    .write_address(mux_reg_wr_addr ? rd : rt),
    .write_data(mux_reg_wr_data ? /* data_mem_out */ : /* alu_out */),
    .read_data_1(read_data1), .read_data_2(read_data2)
  );

  // Sign-extend immediate
  wire [31:0] imm_ext;
  sign_ext se(.in(imm), .out(imm_ext));

  // ALU input MUX
  wire [31:0] alu_src2;
  mux2 #(.WIDTH(32)) mux_alu(
    .d0(read_data2),
    .d1(imm_ext),
    .sel(mux_alu_src),
    .y(alu_src2)
  );

  // ALU
  wire [31:0] alu_out;
  alu alu_unit(
    .a1(read_data1),
    .a2(alu_src2),
    .ctrl(alu_ctrl), // hooked up via alu_ctrl module
    .out(alu_out),
    .zero(alu_zero)
  );

  // Data memory
  wire [31:0] data_mem_out;
  memory data_mem(
    .clk(clk),
    .write_enable(mem_write),
    .read_address(alu_out[11:2]),
    .write_address(alu_out[11:2]),
    .data_in(read_data2),
    .data_out(data_mem_out)
  );

  // PC
  sign_ext se2(.in(imm), .out(imm_ext)); // reuse or new
  PC pc_unit(
    .in_addr(pc_curr),
    .mux_jump(mux_jump),
    .instruction(addr),
    .branch(branch),
    .alu_zero(alu_zero),
    .offset(imm_ext),
    .out_addr(pc_in)
  );

  // PC register
  reg [31:0] PC_reg;
  always @(posedge clk or posedge rst) begin
    if (rst) PC_reg <= 0;
    else      PC_reg <= pc_in;
  end
  assign pc_curr = PC_reg;
  assign pc_out  = pc_curr;
endmodule