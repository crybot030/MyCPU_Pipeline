module mycpu_top(
    input  wire        clk,
    input  wire        resetn,
    // inst sram interface
    output wire        inst_sram_en,
    output wire [ 3:0] inst_sram_we,
    output wire [31:0] inst_sram_addr,
    output wire [31:0] inst_sram_wdata,
    input  wire [31:0] inst_sram_rdata,
    // data sram interface
    output wire        data_sram_en,
    output wire [ 3:0] data_sram_we,
    output wire [31:0] data_sram_addr,
    output wire [31:0] data_sram_wdata,
    input  wire [31:0] data_sram_rdata,
    // trace debug interface
    output wire [31:0] debug_wb_pc,
    output wire [ 3:0] debug_wb_rf_we,
    output wire [ 4:0] debug_wb_rf_wnum,
    output wire [31:0] debug_wb_rf_wdata
);

reg reset;
always @(posedge clk) reset <= ~resetn;

// 全局流水线控制信号声明
wire ID_stall;
wire ID_cancel;
wire real_br_taken;
wire [31:0] ID_br_target;

// ====================================================================
// Forwarding Unit
// ====================================================================

// 前递起点：从各级数据通路的最新结果处提取
wire [31:0] ex_fwd_data = EX_alu_result;
wire [31:0] mem_fwd_data = MEM_final_result;
wire [31:0] wb_fwd_data = WB_final_result;

//前递终点：译码级寄存器堆读出结果生成逻辑
wire [31:0] ID_rj_value;
wire [31:0] ID_rkd_value;

assign ID_rj_value = 
    (EX_valid && EX_gr_we && (EX_dest == rf_raddr1) && (rf_raddr1 != 5'b0)) ? ex_fwd_data : (MEM_valid && MEM_gr_we && (MEM_dest == rf_raddr1) && (rf_raddr1 != 5'b0)) ? mem_fwd_data : (WB_valid && WB_gr_we && (WB_dest == rf_raddr1) && (rf_raddr1 != 5'b0)) ? wb_fwd_data : rf_rdata1;

assign ID_rkd_value = 
    (EX_valid  && EX_gr_we  && (EX_dest == rf_raddr2)  && (rf_raddr2 != 5'd0)) ? ex_fwd_data :
    (MEM_valid && MEM_gr_we && (MEM_dest == rf_raddr2) && (rf_raddr2 != 5'd0)) ? mem_fwd_data :(WB_valid  && WB_gr_we  && (WB_dest == rf_raddr2)  && (rf_raddr2 != 5'd0)) ? wb_fwd_data :rf_rdata2;



// ====================================================================
// Pre-IF / IF Stage
// ====================================================================
reg  [31:0] pc;
wire [31:0] nextpc;
wire [31:0] seq_pc;

assign seq_pc = pc + 32'h4;

// nextpc 逻辑：
// 1. 如果跳转成立（且未被阻塞），则跳到目标地址
// 2. 如果流水线阻塞，PC 保持不变，以便 SRAM 继续读出处于 IF 级的指令
// 3. 正常情况顺序执行
assign nextpc = real_br_taken ? ID_br_target : 
                ID_stall      ? pc : 
                                seq_pc;

always @(posedge clk) begin
    if (reset) begin
        pc <= 32'h1c000000;  // 直接复位到入口地址
    end
    else begin
        pc <= nextpc;
    end
end

assign inst_sram_en    = 1'b1;
assign inst_sram_we    = 4'b0000;
assign inst_sram_addr  = nextpc; 
assign inst_sram_wdata = 32'b0;


// ====================================================================
// IDreg (IF -> ID Pipeline Register)
// ====================================================================
reg [31:0] ID_pc;
reg [31:0] ID_inst;
reg        ID_valid;

always @(posedge clk) begin
    if (reset) begin
        ID_valid <= 1'b0;
        ID_pc    <= 32'b0;
        ID_inst  <= 32'b0;
    end
    // 发生控制跳转，取消转移指令后的下一条指令，将 valid 置 0
    else if (ID_cancel) begin
        ID_valid <= 1'b0;
    end
    // 如果没有阻塞，正常接收 IF 级数据
    else if (!ID_stall) begin
        ID_valid <= 1'b1;
        ID_pc    <= pc;
        ID_inst  <= inst_sram_rdata;
    end
    // 如果 ID_stall 为真，不更新寄存器，保持旧值（实现阻塞）
end


// ====================================================================
// ID Stage
// ====================================================================
wire [ 5:0] ID_op_31_26  = ID_inst[31:26];
wire [ 3:0] ID_op_25_22  = ID_inst[25:22];
wire [ 1:0] ID_op_21_20  = ID_inst[21:20];
wire [ 4:0] ID_op_19_15  = ID_inst[19:15];

wire [ 4:0] ID_rd = ID_inst[ 4: 0];
wire [ 4:0] ID_rj = ID_inst[ 9: 5];
wire [ 4:0] ID_rk = ID_inst[14:10];

wire [11:0] ID_i12 = ID_inst[21:10];
wire [19:0] ID_i20 = ID_inst[24: 5];
wire [15:0] ID_i16 = ID_inst[25:10];
wire [25:0] ID_i26 = {ID_inst[ 9: 0], ID_inst[25:10]};

wire [63:0] ID_op_31_26_d;
wire [15:0] ID_op_25_22_d;
wire [ 3:0] ID_op_21_20_d;
wire [31:0] ID_op_19_15_d;

decoder_6_64 u_dec0(.in(ID_op_31_26 ), .out(ID_op_31_26_d ));
decoder_4_16 u_dec1(.in(ID_op_25_22 ), .out(ID_op_25_22_d ));
decoder_2_4  u_dec2(.in(ID_op_21_20 ), .out(ID_op_21_20_d ));
decoder_5_32 u_dec3(.in(ID_op_19_15 ), .out(ID_op_19_15_d ));

// 算数逻辑指令
wire ID_inst_add_w   = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h00];
wire ID_inst_addi_w  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'ha];
wire ID_inst_sub_w   = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h02];
wire ID_inst_slt     = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h04];
wire ID_inst_sltu    = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h05];
wire ID_inst_nor     = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h08];
wire ID_inst_and     = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h09];
wire ID_inst_or      = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h0a];
wire ID_inst_xor     = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h0b];
wire ID_inst_slti   = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h8];
wire ID_inst_sltui  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h9];
wire ID_inst_andi   = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'hd];
wire ID_inst_ori    = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'he];
wire ID_inst_xori   = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'hf];

// 移位指令
wire ID_inst_slli_w  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h1] & ID_op_21_20_d[2'h0] & ID_op_19_15_d[5'h01];
wire ID_inst_srli_w  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h1] & ID_op_21_20_d[2'h0] & ID_op_19_15_d[5'h09];
wire ID_inst_srai_w  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h1] & ID_op_21_20_d[2'h0] & ID_op_19_15_d[5'h11];
wire ID_inst_sll_w  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h0e];
wire ID_inst_srl_w  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h0f];
wire ID_inst_sra_w  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h10];
wire ID_inst_lu12i_w = ID_op_31_26_d[6'h05] & ~ID_inst[25];

// 存取指令
wire ID_inst_ld_w    = ID_op_31_26_d[6'h0a] & ID_op_25_22_d[4'h2];
wire ID_inst_st_w    = ID_op_31_26_d[6'h0a] & ID_op_25_22_d[4'h6];


// 转移指令
wire ID_inst_b       = ID_op_31_26_d[6'h14];
wire ID_inst_bl      = ID_op_31_26_d[6'h15];
wire ID_inst_beq     = ID_op_31_26_d[6'h16];
wire ID_inst_bne     = ID_op_31_26_d[6'h17];
wire ID_inst_jirl    = ID_op_31_26_d[6'h13];
wire ID_inst_pcaddu12i = ID_op_31_26_d[6'h07] & ~ID_inst[25];

// 乘除法指令
wire ID_inst_mul_w   = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h18];
wire ID_inst_mulh_w  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h19];
wire ID_inst_mulh_wu = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h1a];
wire ID_inst_div_w   = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h2] & ID_op_19_15_d[5'h00];
wire ID_inst_mod_w   = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h2] & ID_op_19_15_d[5'h01];
wire ID_inst_div_wu  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h2] & ID_op_19_15_d[5'h02];
wire ID_inst_mod_wu  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h2] & ID_op_19_15_d[5'h03];

wire [18:0] ID_alu_op;
assign ID_alu_op[ 0] = ID_inst_add_w | ID_inst_addi_w | ID_inst_ld_w | ID_inst_st_w | ID_inst_jirl | ID_inst_bl | ID_inst_pcaddu12i;
assign ID_alu_op[ 1] = ID_inst_sub_w;
assign ID_alu_op[ 2] = ID_inst_slt | ID_inst_slti;
assign ID_alu_op[ 3] = ID_inst_sltu | ID_inst_sltui;
assign ID_alu_op[ 4] = ID_inst_and | ID_inst_andi;
assign ID_alu_op[ 5] = ID_inst_nor;
assign ID_alu_op[ 6] = ID_inst_or | ID_inst_ori;
assign ID_alu_op[ 7] = ID_inst_xor | ID_inst_xori;
assign ID_alu_op[ 8] = ID_inst_slli_w | ID_inst_sll_w;
assign ID_alu_op[ 9] = ID_inst_srli_w | ID_inst_srl_w;
assign ID_alu_op[10] = ID_inst_srai_w | ID_inst_sra_w;
assign ID_alu_op[11] = ID_inst_lu12i_w;
assign ID_alu_op[12] = ID_inst_mul_w;
assign ID_alu_op[13] = ID_inst_mulh_w;
assign ID_alu_op[14] = ID_inst_mulh_wu;
assign ID_alu_op[15] = ID_inst_div_w;
assign ID_alu_op[16] = ID_inst_mod_w;
assign ID_alu_op[17] = ID_inst_div_wu;
assign ID_alu_op[18] = ID_inst_mod_wu;

// 立即数扩展
wire ID_need_ui5   =  ID_inst_slli_w | ID_inst_srli_w | ID_inst_srai_w;
wire ID_need_ui12 = ID_inst_andi | ID_inst_ori | ID_inst_xori; // 无符号/零扩展
wire ID_need_si12  =  ID_inst_addi_w | ID_inst_ld_w | ID_inst_st_w | ID_inst_slti | ID_inst_sltui;
wire ID_need_si16  =  ID_inst_jirl | ID_inst_beq | ID_inst_bne;
wire ID_need_si20  =  ID_inst_lu12i_w | ID_inst_pcaddu12i;
wire ID_need_si26  =  ID_inst_b | ID_inst_bl;
wire ID_src2_is_4  =  ID_inst_jirl | ID_inst_bl;

wire [31:0] ID_imm = 
    ID_src2_is_4      ? 32'h4 :
    ID_need_si20      ? {ID_i20[19:0], 12'b0} :
    ID_need_ui12      ? {20'b0, ID_i12[11:0]} : // 零扩展
                        {{20{ID_i12[11]}}, ID_i12[11:0]} ; // 默认符号扩展

wire [31:0] ID_br_offs  = ID_need_si26 ? {{ 4{ID_i26[25]}}, ID_i26[25:0], 2'b0} :
                                         {{14{ID_i16[15]}}, ID_i16[15:0], 2'b0} ;
wire [31:0] ID_jirl_offs = {{14{ID_i16[15]}}, ID_i16[15:0], 2'b0};

wire ID_src_reg_is_rd = ID_inst_beq | ID_inst_bne | ID_inst_st_w;
wire ID_src1_is_pc    = ID_inst_jirl | ID_inst_bl | ID_inst_pcaddu12i;
wire ID_src2_is_imm = ID_inst_slli_w | ID_inst_srli_w | ID_inst_srai_w | ID_inst_addi_w |
                      ID_inst_ld_w   | ID_inst_st_w   | ID_inst_lu12i_w| ID_inst_jirl | 
                      ID_inst_bl     | ID_inst_slti   | ID_inst_sltui  | ID_inst_andi | 
                      ID_inst_ori    | ID_inst_xori   | ID_inst_pcaddu12i;

wire ID_res_from_mem = ID_inst_ld_w;
wire ID_dst_is_r1    = ID_inst_bl;
wire ID_gr_we        = ~ID_inst_st_w & ~ID_inst_beq & ~ID_inst_bne & ~ID_inst_b ;
wire ID_mem_we       = ID_inst_st_w;
wire [4:0] ID_dest   = ID_dst_is_r1 ? 5'd1 : ID_rd;

wire [ 4:0] rf_raddr1 = ID_rj;
wire [ 4:0] rf_raddr2 = ID_src_reg_is_rd ? ID_rd : ID_rk;
wire [31:0] rf_rdata1;
wire [31:0] rf_rdata2;

wire WB_rf_we;
wire [4:0] WB_rf_waddr;
wire [31:0] WB_rf_wdata;

regfile u_regfile(
    .clk    (clk        ),
    .raddr1 (rf_raddr1  ),
    .rdata1 (rf_rdata1  ),
    .raddr2 (rf_raddr2  ),
    .rdata2 (rf_rdata2  ),
    .we     (WB_rf_we   ),
    .waddr  (WB_rf_waddr),
    .wdata  (WB_rf_wdata)
);

// ====================================================================
// Hazard Detection Unit (阻塞与取消逻辑)
// ====================================================================

// 声明后续阶段寄存器变量，以便于检测使用情况
reg        EX_valid;
reg        EX_gr_we;
reg [ 4:0] EX_dest;
reg        MEM_valid;
reg        MEM_gr_we;
reg [ 4:0] MEM_dest;
reg        WB_valid;
reg        WB_gr_we;
reg [ 4:0] WB_dest;

// 1. 判断当前指令是否实际需要读源寄存器
wire ID_need_rj = ~ID_inst_lu12i_w & ~ID_inst_b & ~ID_inst_bl | ~ID_inst_pcaddu12i;
wire ID_need_rkd = ID_inst_add_w | ID_inst_sub_w | ID_inst_slt | ID_inst_sltu | 
                     ID_inst_nor | ID_inst_and | ID_inst_or | ID_inst_xor | 
                     ID_inst_beq | ID_inst_bne | ID_inst_st_w | 
                     ID_inst_sll_w | ID_inst_srl_w | ID_inst_sra_w | // 新增寄存器移位
                     ID_inst_mul_w | ID_inst_mulh_w | ID_inst_mulh_wu | // 新增乘法
                     ID_inst_div_w | ID_inst_mod_w | ID_inst_div_wu | ID_inst_mod_wu; // 新增除法

// LOAD-USE 冒险检测
assign ID_stall = ID_valid && EX_valid && EX_res_from_mem && (
    (ID_need_rj && (rf_raddr1 != 5'b0) && (EX_dest == rf_raddr1)) || 
    (ID_need_rkd && (rf_raddr2 != 5'b0) && (EX_dest == rf_raddr2))
);

//  控制相关逻辑
wire ID_rj_eq_rd = (ID_rj_value == ID_rkd_value);
wire ID_br_taken = (   ID_inst_beq  &&  ID_rj_eq_rd
                    || ID_inst_bne  && !ID_rj_eq_rd
                    || ID_inst_jirl
                    || ID_inst_bl
                    || ID_inst_b
                   ) && ID_valid;

// 如果发生数据阻塞，寄存器值不可信，此时禁止发生分支跳转
assign real_br_taken = ID_br_taken && !ID_stall;
assign ID_br_target = (ID_inst_beq || ID_inst_bne || ID_inst_bl || ID_inst_b) ? (ID_pc + ID_br_offs) :
                                                                                (ID_rj_value + ID_jirl_offs);

// 若分支确认跳转，将下一拍 IF 到 ID 的 valid 冲刷置零 (Cancel 下一条指令)
assign ID_cancel = real_br_taken;


wire [31:0] ID_alu_src1 = ID_src1_is_pc  ? ID_pc[31:0] : ID_rj_value;
wire [31:0] ID_alu_src2 = ID_src2_is_imm ? ID_imm      : ID_rkd_value;

// ====================================================================
// EXreg (ID -> EX Pipeline Register)
// ====================================================================
reg [31:0] EX_pc;
reg [18:0] EX_alu_op;
reg [31:0] EX_alu_src1;
reg [31:0] EX_alu_src2;
reg        EX_res_from_mem;
reg        EX_mem_we;
reg [31:0] EX_rkd_value;

always @(posedge clk) begin
    if (reset) begin
        EX_valid        <= 1'b0;
        EX_pc           <= 32'b0;
        EX_alu_op       <= 19'b0;
        EX_alu_src1     <= 32'b0;
        EX_alu_src2     <= 32'b0;
        EX_res_from_mem <= 1'b0;
        EX_mem_we       <= 1'b0;
        EX_gr_we        <= 1'b0;
        EX_dest         <= 5'b0;
        EX_rkd_value    <= 32'b0;
    end
    // 阻塞发生时：插入级间气泡，将相关 valid 置 0
    else if (ID_stall) begin
        EX_valid <= 1'b0;
    end
    else begin
        EX_valid        <= ID_valid;
        EX_pc           <= ID_pc;
        EX_alu_op       <= ID_alu_op;
        EX_alu_src1     <= ID_alu_src1;
        EX_alu_src2     <= ID_alu_src2;
        EX_res_from_mem <= ID_res_from_mem;
        EX_mem_we       <= ID_mem_we;
        EX_gr_we        <= ID_gr_we;
        EX_dest         <= ID_dest;
        EX_rkd_value    <= ID_rkd_value;
    end
end


// ====================================================================
// EX Stage
// ====================================================================
wire [31:0] EX_alu_result;

alu u_alu(
    .alu_op     (EX_alu_op    ),
    .alu_src1   (EX_alu_src1  ),
    .alu_src2   (EX_alu_src2  ),
    .alu_result (EX_alu_result)
);

assign data_sram_en    = (EX_res_from_mem || EX_mem_we) && EX_valid;
assign data_sram_we    = (EX_mem_we && EX_valid) ? 4'hF : 4'h0;
assign data_sram_addr  = EX_alu_result;
assign data_sram_wdata = EX_rkd_value;


// ====================================================================
// MEMreg (EX -> MEM Pipeline Register)
// ====================================================================
reg [31:0] MEM_pc;
reg [31:0] MEM_alu_result;
reg        MEM_res_from_mem;

always @(posedge clk) begin
    if (reset) begin
        MEM_valid        <= 1'b0;
        MEM_pc           <= 32'b0;
        MEM_alu_result   <= 32'b0;
        MEM_res_from_mem <= 1'b0;
        MEM_gr_we        <= 1'b0;
        MEM_dest         <= 5'b0;
    end
    else begin
        MEM_valid        <= EX_valid;
        MEM_pc           <= EX_pc;
        MEM_alu_result   <= EX_alu_result;
        MEM_res_from_mem <= EX_res_from_mem;
        MEM_gr_we        <= EX_gr_we;
        MEM_dest         <= EX_dest;
    end
end


// ====================================================================
// MEM Stage
// ====================================================================
wire [31:0] MEM_mem_result;
wire [31:0] MEM_final_result;

assign MEM_mem_result   = data_sram_rdata;
assign MEM_final_result = MEM_res_from_mem ? MEM_mem_result : MEM_alu_result;


// ====================================================================
// WBreg (MEM -> WB Pipeline Register)
// ====================================================================
reg [31:0] WB_pc;
reg [31:0] WB_final_result;

always @(posedge clk) begin
    if (reset) begin
        WB_valid        <= 1'b0;
        WB_pc           <= 32'b0;
        WB_final_result <= 32'b0;
        WB_gr_we        <= 1'b0;
        WB_dest         <= 5'b0;
    end
    else begin
        WB_valid        <= MEM_valid;
        WB_pc           <= MEM_pc;
        WB_final_result <= MEM_final_result;
        WB_gr_we        <= MEM_gr_we;
        WB_dest         <= MEM_dest;
    end
end


// ====================================================================
// WB Stage
// ====================================================================
assign WB_rf_we    = WB_gr_we && WB_valid;
assign WB_rf_waddr = WB_dest;
assign WB_rf_wdata = WB_final_result;

// debug info generate
assign debug_wb_pc       = WB_pc;
assign debug_wb_rf_we    = {4{WB_rf_we}};
assign debug_wb_rf_wnum  = WB_dest;
assign debug_wb_rf_wdata = WB_final_result;

endmodule