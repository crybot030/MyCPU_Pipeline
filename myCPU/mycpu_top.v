module mycpu_top(
    input  wire        clk,
    input  wire        resetn,
    // inst sram interface
    output wire        inst_sram_en,     // 新增：指令RAM片选使能
    output wire [ 3:0] inst_sram_we,     // 修改：4位写使能
    output wire [31:0] inst_sram_addr,
    output wire [31:0] inst_sram_wdata,
    input  wire [31:0] inst_sram_rdata,
    // data sram interface
    output wire        data_sram_en,     // 新增：数据RAM片选使能
    output wire [ 3:0] data_sram_we,     // 修改：4位写使能
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

// ====================================================================
// Pre-IF / IF Stage
// ====================================================================
reg  [31:0] pc;
wire [31:0] nextpc;
wire [31:0] seq_pc;

always @(posedge clk) begin
    if (reset) begin
        pc <= 32'h1c000000;
    end
    else begin
        pc <= nextpc;
    end
end

assign seq_pc = pc + 32'h4;
// nextpc由ID阶段的跳转逻辑决定（不考虑延迟槽刷新，按无冲突处理）
assign nextpc = ID_br_taken ? ID_br_target : seq_pc;

// 采用同步SRAM读：用nextpc作为读地址。由于SRAM有1周期延迟，
// 当下一周期PC跳变到nextpc时，SRAM刚好吐出对应指令数据。
assign inst_sram_en    = 1'b1;         // 恒定使能取指
assign inst_sram_we    = 4'b0000;      // 指令存储器只读
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
    else begin
        ID_valid <= 1'b1;               // 恒定为1，不考虑冲突引发的阻塞
        ID_pc    <= pc;
        ID_inst  <= inst_sram_rdata;
    end
end


// ====================================================================
// ID Stage
// ====================================================================
wire [ 5:0] ID_op_31_26;
wire [ 3:0] ID_op_25_22;
wire [ 1:0] ID_op_21_20;
wire [ 4:0] ID_op_19_15;

wire [ 4:0] ID_rd;
wire [ 4:0] ID_rj;
wire [ 4:0] ID_rk;

wire [11:0] ID_i12;
wire [19:0] ID_i20;
wire [15:0] ID_i16;
wire [25:0] ID_i26;

wire [63:0] ID_op_31_26_d;
wire [15:0] ID_op_25_22_d;
wire [ 3:0] ID_op_21_20_d;
wire [31:0] ID_op_19_15_d;

assign ID_op_31_26  = ID_inst[31:26];
assign ID_op_25_22  = ID_inst[25:22];
assign ID_op_21_20  = ID_inst[21:20];
assign ID_op_19_15  = ID_inst[19:15];

assign ID_rd  = ID_inst[ 4: 0];
assign ID_rj  = ID_inst[ 9: 5];
assign ID_rk  = ID_inst[14:10];

assign ID_i12 = ID_inst[21:10];
assign ID_i20 = ID_inst[24: 5];
assign ID_i16 = ID_inst[25:10];
assign ID_i26 = {ID_inst[ 9: 0], ID_inst[25:10]};

decoder_6_64 u_dec0(.in(ID_op_31_26 ), .out(ID_op_31_26_d ));
decoder_4_16 u_dec1(.in(ID_op_25_22 ), .out(ID_op_25_22_d ));
decoder_2_4  u_dec2(.in(ID_op_21_20 ), .out(ID_op_21_20_d ));
decoder_5_32 u_dec3(.in(ID_op_19_15 ), .out(ID_op_19_15_d ));

wire ID_inst_add_w, ID_inst_sub_w, ID_inst_slt, ID_inst_sltu;
wire ID_inst_nor, ID_inst_and, ID_inst_or, ID_inst_xor;
wire ID_inst_slli_w, ID_inst_srli_w, ID_inst_srai_w, ID_inst_addi_w;
wire ID_inst_ld_w, ID_inst_st_w, ID_inst_jirl, ID_inst_b, ID_inst_bl;
wire ID_inst_beq, ID_inst_bne, ID_inst_lu12i_w;

assign ID_inst_add_w   = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h00];
assign ID_inst_sub_w   = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h02];
assign ID_inst_slt     = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h04];
assign ID_inst_sltu    = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h05];
assign ID_inst_nor     = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h08];
assign ID_inst_and     = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h09];
assign ID_inst_or      = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h0a];
assign ID_inst_xor     = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h0] & ID_op_21_20_d[2'h1] & ID_op_19_15_d[5'h0b];
assign ID_inst_slli_w  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h1] & ID_op_21_20_d[2'h0] & ID_op_19_15_d[5'h01];
assign ID_inst_srli_w  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h1] & ID_op_21_20_d[2'h0] & ID_op_19_15_d[5'h09];
assign ID_inst_srai_w  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'h1] & ID_op_21_20_d[2'h0] & ID_op_19_15_d[5'h11];
assign ID_inst_addi_w  = ID_op_31_26_d[6'h00] & ID_op_25_22_d[4'ha];
assign ID_inst_ld_w    = ID_op_31_26_d[6'h0a] & ID_op_25_22_d[4'h2];
assign ID_inst_st_w    = ID_op_31_26_d[6'h0a] & ID_op_25_22_d[4'h6];
assign ID_inst_jirl    = ID_op_31_26_d[6'h13];
assign ID_inst_b       = ID_op_31_26_d[6'h14];
assign ID_inst_bl      = ID_op_31_26_d[6'h15];
assign ID_inst_beq     = ID_op_31_26_d[6'h16];
assign ID_inst_bne     = ID_op_31_26_d[6'h17];
assign ID_inst_lu12i_w = ID_op_31_26_d[6'h05] & ~ID_inst[25];

wire [11:0] ID_alu_op;
assign ID_alu_op[ 0] = ID_inst_add_w | ID_inst_addi_w | ID_inst_ld_w | ID_inst_st_w | ID_inst_jirl | ID_inst_bl;
assign ID_alu_op[ 1] = ID_inst_sub_w;
assign ID_alu_op[ 2] = ID_inst_slt;
assign ID_alu_op[ 3] = ID_inst_sltu;
assign ID_alu_op[ 4] = ID_inst_and;
assign ID_alu_op[ 5] = ID_inst_nor;
assign ID_alu_op[ 6] = ID_inst_or;
assign ID_alu_op[ 7] = ID_inst_xor;
assign ID_alu_op[ 8] = ID_inst_slli_w;
assign ID_alu_op[ 9] = ID_inst_srli_w;
assign ID_alu_op[10] = ID_inst_srai_w;
assign ID_alu_op[11] = ID_inst_lu12i_w;

wire ID_need_ui5   =  ID_inst_slli_w | ID_inst_srli_w | ID_inst_srai_w;
wire ID_need_si12  =  ID_inst_addi_w | ID_inst_ld_w | ID_inst_st_w;
wire ID_need_si16  =  ID_inst_jirl | ID_inst_beq | ID_inst_bne;
wire ID_need_si20  =  ID_inst_lu12i_w;
wire ID_need_si26  =  ID_inst_b | ID_inst_bl;
wire ID_src2_is_4  =  ID_inst_jirl | ID_inst_bl;

wire [31:0] ID_imm = ID_src2_is_4 ? 32'h4 :
                     ID_need_si20 ? {ID_i20[19:0], 12'b0} :
                     /*need_ui5 || need_si12*/{{20{ID_i12[11]}}, ID_i12[11:0]} ;

wire [31:0] ID_br_offs  = ID_need_si26 ? {{ 4{ID_i26[25]}}, ID_i26[25:0], 2'b0} :
                                         {{14{ID_i16[15]}}, ID_i16[15:0], 2'b0} ;
wire [31:0] ID_jirl_offs = {{14{ID_i16[15]}}, ID_i16[15:0], 2'b0};

wire ID_src_reg_is_rd = ID_inst_beq | ID_inst_bne | ID_inst_st_w;
wire ID_src1_is_pc    = ID_inst_jirl | ID_inst_bl;
wire ID_src2_is_imm   = ID_inst_slli_w | ID_inst_srli_w | ID_inst_srai_w | ID_inst_addi_w |
                        ID_inst_ld_w   | ID_inst_st_w   | ID_inst_lu12i_w| ID_inst_jirl   | ID_inst_bl;

wire ID_res_from_mem = ID_inst_ld_w;
wire ID_dst_is_r1    = ID_inst_bl;
wire ID_gr_we        = ~ID_inst_st_w & ~ID_inst_beq & ~ID_inst_bne & ~ID_inst_b ;
wire ID_mem_we       = ID_inst_st_w;
wire [4:0] ID_dest   = ID_dst_is_r1 ? 5'd1 : ID_rd;

wire [ 4:0] rf_raddr1 = ID_rj;
wire [ 4:0] rf_raddr2 = ID_src_reg_is_rd ? ID_rd : ID_rk;
wire [31:0] rf_rdata1;
wire [31:0] rf_rdata2;

// 注意写回端接到 WB 级的信号
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

wire [31:0] ID_rj_value  = rf_rdata1;
wire [31:0] ID_rkd_value = rf_rdata2;

wire ID_rj_eq_rd = (ID_rj_value == ID_rkd_value);
wire ID_br_taken;
wire [31:0] ID_br_target;

assign ID_br_taken = (   ID_inst_beq  &&  ID_rj_eq_rd
                      || ID_inst_bne  && !ID_rj_eq_rd
                      || ID_inst_jirl
                      || ID_inst_bl
                      || ID_inst_b
                     ) && ID_valid;
assign ID_br_target = (ID_inst_beq || ID_inst_bne || ID_inst_bl || ID_inst_b) ? (ID_pc + ID_br_offs) :
                                                                                (ID_rj_value + ID_jirl_offs);

wire [31:0] ID_alu_src1 = ID_src1_is_pc  ? ID_pc[31:0] : ID_rj_value;
wire [31:0] ID_alu_src2 = ID_src2_is_imm ? ID_imm      : ID_rkd_value;


// ====================================================================
// EXreg (ID -> EX Pipeline Register)
// ====================================================================
reg [31:0] EX_pc;
reg [11:0] EX_alu_op;
reg [31:0] EX_alu_src1;
reg [31:0] EX_alu_src2;
reg        EX_res_from_mem;
reg        EX_mem_we;
reg        EX_gr_we;
reg [ 4:0] EX_dest;
reg [31:0] EX_rkd_value;
reg        EX_valid;

always @(posedge clk) begin
    if (reset) begin
        EX_valid        <= 1'b0;
        EX_pc           <= 32'b0;
        EX_alu_op       <= 12'b0;
        EX_alu_src1     <= 32'b0;
        EX_alu_src2     <= 32'b0;
        EX_res_from_mem <= 1'b0;
        EX_mem_we       <= 1'b0;
        EX_gr_we        <= 1'b0;
        EX_dest         <= 5'b0;
        EX_rkd_value    <= 32'b0;
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

// SRAM 具有同步读写属性。因此EX级提供地址和控制信号，下一周期(MEM)刚好获取读出数据
assign data_sram_en    = (EX_res_from_mem || EX_mem_we) && EX_valid;
assign data_sram_we    = (EX_mem_we && EX_valid) ? 4'hF : 4'h0; // 访存且有效时写字节全通
assign data_sram_addr  = EX_alu_result;
assign data_sram_wdata = EX_rkd_value;


// ====================================================================
// MEMreg (EX -> MEM Pipeline Register)
// ====================================================================
reg [31:0] MEM_pc;
reg [31:0] MEM_alu_result;
reg        MEM_res_from_mem;
reg        MEM_gr_we;
reg [ 4:0] MEM_dest;
reg        MEM_valid;

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

// 同步SRAM在这一拍返回由EX阶段发出地址的数据
assign MEM_mem_result   = data_sram_rdata;
assign MEM_final_result = MEM_res_from_mem ? MEM_mem_result : MEM_alu_result;


// ====================================================================
// WBreg (MEM -> WB Pipeline Register)
// ====================================================================
reg [31:0] WB_pc;
reg [31:0] WB_final_result;
reg        WB_gr_we;
reg [ 4:0] WB_dest;
reg        WB_valid;

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
wire        WB_rf_we;
wire [ 4:0] WB_rf_waddr;
wire [31:0] WB_rf_wdata;

assign WB_rf_we    = WB_gr_we && WB_valid;
assign WB_rf_waddr = WB_dest;
assign WB_rf_wdata = WB_final_result;

// debug info generate
assign debug_wb_pc       = WB_pc;
assign debug_wb_rf_we    = {4{WB_rf_we}};
assign debug_wb_rf_wnum  = WB_dest;
assign debug_wb_rf_wdata = WB_final_result;

endmodule