logic csr_misa;
logic csr_mvendorid;
logic csr_marchid;
logic csr_mimpid;
logic csr_mhartid;
logic csr_mstatus;
logic csr_mtvec;
logic csr_mip;
logic csr_mie;
logic csr_mcyclel;
logic csr_mcycleh;
logic csr_minstretl;
logic csr_minstreth;
logic csr_mscratch;
logic csr_mepc;
logic csr_mcause;
logic csr_mscause;
logic csr_mtval;
logic csr_mrac;
logic csr_dmst;
logic csr_mdseac;
logic csr_meihap;
logic csr_meivt;
logic csr_meipt;
logic csr_meicurpl;
logic csr_meicidpl;
logic csr_dcsr;
logic csr_mcgc;
logic csr_mfdc;
logic csr_dpc;
logic csr_mtsel;
logic csr_mtdata1;
logic csr_mtdata2;
logic csr_mhpmc3;
logic csr_mhpmc4;
logic csr_mhpmc5;
logic csr_mhpmc6;
logic csr_mhpmc3h;
logic csr_mhpmc4h;
logic csr_mhpmc5h;
logic csr_mhpmc6h;
logic csr_mhpme3;
logic csr_mhpme4;
logic csr_mhpme5;
logic csr_mhpme6;
logic csr_mcountinhibit;
logic csr_mitctl0;
logic csr_mitctl1;
logic csr_mitb0;
logic csr_mitb1;
logic csr_mitcnt0;
logic csr_mitcnt1;
logic csr_perfva;
logic csr_perfvb;
logic csr_perfvc;
logic csr_perfvd;
logic csr_perfve;
logic csr_perfvf;
logic csr_perfvg;
logic csr_perfvh;
logic csr_perfvi;
logic csr_mpmc;
logic csr_mcpc;
logic csr_meicpct;
logic csr_mdeau;
logic csr_micect;
logic csr_miccmect;
logic csr_mdccmect;
logic csr_mfdht;
logic csr_mfdhs;
logic csr_dicawics;
logic csr_dicad0h;
logic csr_dicad0;
logic csr_dicad1;
logic csr_dicago;
logic csr_pmpcfg;
logic csr_pmpaddr0;
logic csr_pmpaddr16;
logic csr_pmpaddr32;
logic csr_pmpaddr48;
logic valid_only;
logic presync;
logic postsync;
assign csr_misa = (!dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[0]);

assign csr_mvendorid = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]);

assign csr_marchid = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mimpid = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[6]
    &dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]);

assign csr_mhartid = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[2]);

assign csr_mstatus = (!dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[2]&!dec_csr_rdaddr_d[0]);

assign csr_mtvec = (!dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[0]);

assign csr_mip = (!dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[2]);

assign csr_mie = (!dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]
    &dec_csr_rdaddr_d[2]&!dec_csr_rdaddr_d[0]);

assign csr_mcyclel = (dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[1]);

assign csr_mcycleh = (dec_csr_rdaddr_d[7]&!dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[2]&!dec_csr_rdaddr_d[1]);

assign csr_minstretl = (!dec_csr_rdaddr_d[7]&!dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_minstreth = (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mscratch = (!dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[2]&!dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mepc = (!dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[1]
    &dec_csr_rdaddr_d[0]);

assign csr_mcause = (!dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[6]
    &dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mscause = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[5]
    &dec_csr_rdaddr_d[2]);

assign csr_mtval = (!dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[1]
    &dec_csr_rdaddr_d[0]);

assign csr_mrac = (!dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[10]
    &!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[1]);

assign csr_dmst = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]
    &dec_csr_rdaddr_d[2]&!dec_csr_rdaddr_d[1]);

assign csr_mdseac = (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[10]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]);

assign csr_meihap = (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[10]
    &dec_csr_rdaddr_d[3]);

assign csr_meivt = (dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]
    &dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_meipt = (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[1]
    &dec_csr_rdaddr_d[0]);

assign csr_meicurpl = (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[6]
    &dec_csr_rdaddr_d[2]);

assign csr_meicidpl = (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[6]
    &dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]);

assign csr_dcsr = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[5]
    &dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[0]);

assign csr_mcgc = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[4]&dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[0]);

assign csr_mfdc = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[4]&dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]);

assign csr_dpc = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[5]
    &dec_csr_rdaddr_d[4]&dec_csr_rdaddr_d[0]);

assign csr_mtsel = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]
    &!dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mtdata1 = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[4]
    &!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[0]);

assign csr_mtdata2 = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[5]
    &!dec_csr_rdaddr_d[4]&dec_csr_rdaddr_d[1]);

assign csr_mhpmc3 = (dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[0]);

assign csr_mhpmc4 = (dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mhpmc5 = (dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[1]
    &dec_csr_rdaddr_d[0]);

assign csr_mhpmc6 = (!dec_csr_rdaddr_d[7]&!dec_csr_rdaddr_d[5]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mhpmc3h = (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[0]);

assign csr_mhpmc4h = (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mhpmc5h = (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[1]
    &dec_csr_rdaddr_d[0]);

assign csr_mhpmc6h = (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mhpme3 = (!dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[5]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[0]);

assign csr_mhpme4 = (!dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[5]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mhpme5 = (!dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[5]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[1]
    &dec_csr_rdaddr_d[0]);

assign csr_mhpme6 = (!dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[5]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[1]
    &!dec_csr_rdaddr_d[0]);

assign csr_mcountinhibit = (!dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[5]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[0]);

assign csr_mitctl0 = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[6]
    &dec_csr_rdaddr_d[4]&dec_csr_rdaddr_d[2]&!dec_csr_rdaddr_d[1]
    &!dec_csr_rdaddr_d[0]);

assign csr_mitctl1 = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[3]
    &dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]);

assign csr_mitb0 = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]);

assign csr_mitb1 = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[4]&dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mitcnt0 = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[0]);

assign csr_mitcnt1 = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]);

assign csr_perfva  = 1'b0;

assign csr_perfvb  = 1'b0;

assign csr_perfvc  = 1'b0;

assign csr_perfvd  = 1'b0;

assign csr_perfve  = 1'b0;

assign csr_perfvf  = 1'b0;

assign csr_perfvg  = 1'b0;

assign csr_perfvh  = 1'b0;

assign csr_perfvi  = 1'b0;

assign csr_mpmc = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]
    &dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[1]);

assign csr_mcpc = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]
    &!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[1]);

assign csr_meicpct = (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[6]
    &dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mdeau = (dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]
    &dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[3]);

assign csr_micect = (dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[4]
    &!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_miccmect = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[6]
    &dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[0]);

assign csr_mdccmect = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[5]
    &dec_csr_rdaddr_d[4]&dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mfdht = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_mfdhs = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[4]
    &dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[0]);

assign csr_dicawics = (!dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[10]
    &!dec_csr_rdaddr_d[4]&dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_dicad0h = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[3]
    &dec_csr_rdaddr_d[2]&!dec_csr_rdaddr_d[1]);

assign csr_dicad0 = (dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[4]
    &dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]);

assign csr_dicad1 = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign csr_dicago = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]);

assign csr_pmpcfg = (!dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]);

assign csr_pmpaddr0 = (!dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[4]);

assign csr_pmpaddr16 = (!dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]
    &dec_csr_rdaddr_d[7]&!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]);

assign csr_pmpaddr32 = (!dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[6]
    &dec_csr_rdaddr_d[4]);

assign csr_pmpaddr48 = (dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[5]
    &!dec_csr_rdaddr_d[4]);

assign valid_only = (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]) | (dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[4]) | (
    !dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[4]) | (
    !dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[3]) | (
    !dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[1]
    &dec_csr_rdaddr_d[0]) | (!dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[3]);

assign presync = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[4]&dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]) | (dec_csr_rdaddr_d[10]
    &!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[1]) | (!dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[2]&!dec_csr_rdaddr_d[0]) | (dec_csr_rdaddr_d[10]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[0]) | (
    dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[0]) | (dec_csr_rdaddr_d[11]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[1]) | (dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[4]
    &!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]);

assign postsync = (dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[4]&dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]) | (!dec_csr_rdaddr_d[11]
    &!dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[0]) | (!dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[2]&!dec_csr_rdaddr_d[0]) | (dec_csr_rdaddr_d[10]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[0]) | (
    !dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[5]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[1]) | (
    dec_csr_rdaddr_d[10]&!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]
    &!dec_csr_rdaddr_d[2]&dec_csr_rdaddr_d[1]) | (!dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]);

logic legal;
assign legal = (!dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[9]
    &dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[6]
    &dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]) | (!dec_csr_rdaddr_d[10]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]
    &dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]) | (
    !dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[9]
    &dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[1]
    &!dec_csr_rdaddr_d[0]) | (!dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&!dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]
    &!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[1]) | (dec_csr_rdaddr_d[11]
    &!dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]
    &!dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[0]) | (
    !dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]
    &dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]
    &!dec_csr_rdaddr_d[4]&dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]) | (
    !dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[9]
    &dec_csr_rdaddr_d[8]&!dec_csr_rdaddr_d[7]&!dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[1]
    &!dec_csr_rdaddr_d[0]) | (!dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]) | (!dec_csr_rdaddr_d[11]
    &dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]
    &dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[5]
    &dec_csr_rdaddr_d[4]&dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[1]&dec_csr_rdaddr_d[0]) | (!dec_csr_rdaddr_d[11]
    &dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]
    &dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[5]
    &dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[2]&!dec_csr_rdaddr_d[1]) | (
    dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]
    &!dec_csr_rdaddr_d[7]&!dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]
    &dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[0]) | (dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[9]
    &dec_csr_rdaddr_d[8]&!dec_csr_rdaddr_d[7]&!dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]
    &dec_csr_rdaddr_d[2]&!dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]) | (
    dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]
    &!dec_csr_rdaddr_d[7]&!dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]
    &dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &dec_csr_rdaddr_d[1]) | (!dec_csr_rdaddr_d[11]&dec_csr_rdaddr_d[9]
    &dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[7]&!dec_csr_rdaddr_d[6]
    &dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[1]) | (!dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&!dec_csr_rdaddr_d[6]
    &dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[2]) | (!dec_csr_rdaddr_d[11]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[4]
    &!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[2]) | (!dec_csr_rdaddr_d[11]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]
    &dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[1]) | (!dec_csr_rdaddr_d[11]
    &!dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]
    &!dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[1]
    &dec_csr_rdaddr_d[0]) | (dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&!dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[2]) | (!dec_csr_rdaddr_d[11]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[4]
    &!dec_csr_rdaddr_d[3]&dec_csr_rdaddr_d[1]) | (dec_csr_rdaddr_d[9]
    &dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[7]&dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[2]
    &!dec_csr_rdaddr_d[1]&!dec_csr_rdaddr_d[0]) | (!dec_csr_rdaddr_d[11]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]
    &!dec_csr_rdaddr_d[0]) | (dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&!dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[1]) | (!dec_csr_rdaddr_d[11]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]
    &dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]) | (!dec_csr_rdaddr_d[11]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[7]
    &!dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[5]&!dec_csr_rdaddr_d[4]
    &!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]&!dec_csr_rdaddr_d[0]) | (
    !dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[9]
    &dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]
    &!dec_csr_rdaddr_d[4]&!dec_csr_rdaddr_d[3]&!dec_csr_rdaddr_d[2]) | (
    !dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[9]
    &dec_csr_rdaddr_d[8]&!dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[5]
    &dec_csr_rdaddr_d[3]) | (dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&!dec_csr_rdaddr_d[6]
    &!dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[3]) | (!dec_csr_rdaddr_d[11]
    &!dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]
    &!dec_csr_rdaddr_d[6]&dec_csr_rdaddr_d[5]&dec_csr_rdaddr_d[4]) | (
    dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]&dec_csr_rdaddr_d[9]
    &dec_csr_rdaddr_d[8]&!dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]
    &dec_csr_rdaddr_d[4]) | (!dec_csr_rdaddr_d[11]&!dec_csr_rdaddr_d[10]
    &dec_csr_rdaddr_d[9]&dec_csr_rdaddr_d[8]&dec_csr_rdaddr_d[7]
    &dec_csr_rdaddr_d[6]&!dec_csr_rdaddr_d[5]);

