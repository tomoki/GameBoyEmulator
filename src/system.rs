
// Helper functions
// Expand u8 to u16, but for signed operations if the first bit is 1
// then fill the first byte with 1.
// 0xxxxxxx -> 000000000xxxxxxx
// 1xxxxxxx -> 111111111xxxxxxx
fn expand_to_u16_retaining_sign(u : u8) -> u16 {
    if u & (1 << 7) != 0 {
        (u as u16) | 0xFF00
    } else {
        u as u16
    }
}

struct Regs {
    a: u8,
    b: u8,
    c: u8,
    d: u8,
    e: u8,
    h: u8,
    l: u8,
    f: u8,

    pc: u16,
    sp: u16,

    // clock for last instr
    lt: u8,
    // clock
    t : u32,
}

const FLAG_ZERO : u8 = 1 << 7;
const FLAG_N : u8 = 1 << 6;
const FLAG_HALF_CARRY : u8 = 1 << 5;
const FLAG_CARRY : u8 = 1 << 4;

impl Regs {
    fn new() -> Regs {
        Regs {
            a: 0,
            b: 0,
            c: 0,
            d: 0,
            e: 0,
            h: 0,
            l: 0,
            f: 0,

            pc: 0,
            sp: 0,

            lt: 0,
            t: 0
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum Register {
    A, B, C, D, E, H, L, F, PC, SP, LT
}

enum GpuMode {
    ScanlineAccessingOAM,  // number 2
    ScanlineAccessingVRAM, // number 3
    HorizontalBlank,       // number 0
    VerticalBlank,         // number 1
}

const VRAM_START : u16 = 0x8000;
const VRAM_END : u16 = 0x9FFF;
const MAPPED_IO_START: u16 = 0xFF00;
const MAPPED_IO_END : u16 = 0xFF79;
const MEMORY_ZERO_START : u16 = 0xFF80;
const MEMORY_ZERO_END : u16 = 0xFFFF;

const VRAM_SIZE : u16 = VRAM_END - VRAM_START + 1;
const MAPPED_IO_SIZE : u16 = MAPPED_IO_END - MAPPED_IO_START + 1;
const MEMORY_ZERO_SIZE : u16 = MEMORY_ZERO_END - MEMORY_ZERO_START + 1;

pub struct SystemOnChip {
    regs: Regs,
    // Between reset and the first read from 0x0100, then
    // 0x0000 - 0x0100 is mapped to bios.
    pub read_from_bios: bool,

    // memory
    // 0x8000 - 0x9FFF
    vram: [u8; VRAM_SIZE as usize],
    // 0xFF00 - 0xFF79
    mapped_io: [u8; MAPPED_IO_SIZE as usize],
    // 0xFF80 - 0xFFFF
    memory_zero: [u8; MEMORY_ZERO_SIZE as usize],
    cart: Vec<u8>,
    bios: [u8; 256],

    // GPU
    gpu_screen: [u8; 160 * 144],
    gpu_mode: GpuMode,
    gpu_mode_clock: u16,
    gpu_line: u8,
}

impl SystemOnChip {
    // CPU instructions

    // Helper functions
    fn flag_clear(&mut self) -> () {
        self.write_r8(Register::F, 0);
    }

    fn flag_set(&mut self, flag: u8, set: bool) -> () {
        let cur = self.read_r8(Register::F);
        if set {
            self.write_r8(Register::F, cur | flag);
        } else {
            self.write_r8(Register::F, cur & !flag);
        }
    }

    fn flag_is_set(&mut self, flag: u8) -> bool {
        (self.read_r8(Register::F) & flag) != 0
    }

    fn read_r8(&self, r: Register) -> u8 {
        match r {
            Register::A => self.regs.a,
            Register::B => self.regs.b,
            Register::C => self.regs.c,
            Register::D => self.regs.d,
            Register::E => self.regs.e,
            Register::F => self.regs.f,
            Register::H => self.regs.h,
            Register::L => self.regs.l,
            Register::LT => self.regs.lt,
            _ => {
                panic!();
            }
        }
    }

    fn read_r16(&self, r: Register) -> u16 {
        match r {
            Register::SP => self.regs.sp,
            Register::PC => self.regs.pc,
            _ => {
                // 8 bits
                panic!();
            }
        }
    }

    fn read_r16_2(&self, x: Register, y: Register) -> u16 {
        let xv = self.read_r8(x);
        let yv = self.read_r8(y);

        // FIXME: little endian?
        ((xv as u16) << 8) | (yv as u16)
    }

    fn write_r8(&mut self, r: Register, v: u8) -> () {
        match r {
            Register::A => self.regs.a = v,
            Register::B => self.regs.b = v,
            Register::C => self.regs.c = v,
            Register::D => self.regs.d = v,
            Register::E => self.regs.e = v,
            Register::F => self.regs.f = v,
            Register::H => self.regs.h = v,
            Register::L => self.regs.l = v,
            Register::LT => self.regs.lt = v,
            _ => {
                // 16 bits register
                panic!();
            }
        }
    }

    fn write_r16(&mut self, r: Register, v: u16) -> () {
        match r {
            Register::SP => self.regs.sp = v,
            Register::PC => self.regs.pc = v,
            _ => {
                // 8 bits
                panic!();
            }
        }
    }

    fn write_r16_2(&mut self, x: Register, y: Register, v: u16) -> () {
        self.write_r8(x, ((v >> 8) & 0x00FF) as u8);
        self.write_r8(y, (v & 0x00FF) as u8);
    }

   fn set_proc_clock(&mut self, clock : u8) -> () {
        self.write_r8(Register::LT, clock)
    }

    fn get_proc_clock(&self) -> u8 {
        self.read_r8(Register::LT)
    }

    fn push_u8(&mut self, val: u8) -> () {
        let new_addr = self.read_r16(Register::SP) - 1;
        self.write_r16(Register::SP, new_addr);
        self.wb(new_addr, val);
    }

    fn pop_u8(&mut self) -> u8 {
        let cur_addr = self.read_r16(Register::SP);
        let ret = self.rb(cur_addr);
        let new_addr = cur_addr + 1;
        self.write_r16(Register::SP, new_addr);

        ret
    }

    fn push_u16(&mut self, val: u16) -> () {
        // little endian.
        self.push_u8((val >> 8) as u8);
        self.push_u8((val & 0xFF) as u8);
    }

    fn pop_u16(&mut self) -> u16 {
        let l = self.pop_u8();
        let h = self.pop_u8();

        ((h as u16) << 8) | (l as u16)
    }

    fn proceed_pc(&mut self, n: u16) -> () {
        let cur = self.read_r16(Register::PC);
        let nex = cur + n;
        self.write_r16(Register::PC, nex);
    }

    fn read_u8_pc(&mut self) -> u8 {
        let ret = self.rb(self.read_r16(Register::PC));
        self.proceed_pc(1);
        ret
    }

    fn read_u16_pc(&mut self) -> u16 {
        let low = self.read_u8_pc();
        let hig = self.read_u8_pc();
        ((hig as u16) << 8) | (low as u16)
    }

    // Each instructions have a following information
    // - Bytes for instr
    // - Assembler human readable instr
    // - Affect: Ordered by Z N H C. 0, 1 means it should be reset/set. - means doesn't affect.
    // - CPU Clock: CPU clock (t clock) used
    // - Bytes: From how many bytes is the instr constructed?

    // generalized functions
    // --
    // LD XY, d16
    // Affect: - - - -
    // CPU Clock: -
    // Bytes: 3
    fn ld_xy_d16(&mut self, x: Register, y: Register) -> () {
        let high = self.read_u8_pc();
        let low = self.read_u8_pc();

        // FIXME: little endian?
        self.write_r8(y, high);
        self.write_r8(x, low);

    }

    // LD X, Y
    // Affect: - - - -
    // CPU Clock: -
    // Bytes: 1
    fn ld_x_y(&mut self, x: Register, y: Register) -> () {
        self.write_r8(x, self.read_r8(y))
    }

    // PUSH XY
    // Affect: - - - -
    // CPU Clock: -
    // Bytes: 1
    fn push_xy(&mut self, x: Register, y: Register) -> () {
        self.push_u8(self.read_r8(x));
        self.push_u8(self.read_r8(y));
    }

    // POP XY
    // Affect: - - - -
    // CPU Clock: -
    // Bytes: 1
    fn pop_xy(&mut self, x: Register, y: Register) -> () {
        let ty = self.pop_u8();
        let tx = self.pop_u8();
        self.write_r8(y, ty);
        self.write_r8(x, tx);
    }

    // LD X,d8
    // Affect: - - - -
    // CPU Clock: -
    // Bytes: 2
    fn ld_x_d8(&mut self, x: Register) -> () {
        let n = self.read_u8_pc();
        self.write_r8(x, n);
    }

    // RL X
    // Affect: Z 0 0 C
    // CPU Clock: -
    // Bytes: 2
    fn rl_x(&mut self, x: Register) -> () {
        let n = self.read_r8(x);
        let old_carry_flag = self.flag_is_set(FLAG_CARRY);

        self.flag_set(FLAG_ZERO, n == 0);
        self.flag_set(FLAG_N, false);
        self.flag_set(FLAG_HALF_CARRY, false);
        self.flag_set(FLAG_CARRY, (n & (1 << 7)) != 0);

        self.write_r8(x, (n << 1) | (if old_carry_flag { 1 } else { 0 }));
    }

    // LD A, (XY)
    // Affect - - - -
    // CPU Clock: 8
    // Bytes: 1
    fn ld_a_addr_xy(&mut self, x: Register, y: Register) -> () {
        let addr = self.read_r16_2(x, y);
        let valu = self.rb(addr);
        self.write_r8(Register::A, valu);
        self.set_proc_clock(8);
    }

    // INC X
    // Affect: Z 0 H -
    // CPU Clock: -
    // Bytes: 1
    fn inc_x(&mut self, x: Register) -> () {
        let n = self.read_r8(x);

        self.flag_set(FLAG_ZERO, n == 0xFF);
        self.flag_set(FLAG_N, false);
        // 1 if carry from bit 3 == bit 0 ~ bit 3 is 1.
        self.flag_set(FLAG_HALF_CARRY, (n & 0x0F) == 0x0F);

        self.write_r8(x, n.wrapping_add(1));
    }

    // DEC X
    // Affect: Z 1 H -
    // CPU Clock: -
    // Bytes: 1
    fn dec_x(&mut self, x: Register) -> () {
        let n = self.read_r8(x);

        self.flag_set(FLAG_ZERO, n == 1);
        self.flag_set(FLAG_N, true);
        // 1 if borrow from bit 4 == bit 0 ~ bit 3 is 0.
        self.flag_set(FLAG_HALF_CARRY, (n & 0x0F) == 0);

        self.write_r8(x, n.wrapping_sub(1));
    }

    // INC XY
    // Affect: - - - -
    // CPU Clock: -
    // Bytes: 2
    fn inc_xy(&mut self, x: Register, y: Register) -> () {
        let n = self.read_r16_2(x, y);
        let new_n = n.wrapping_add(1);
        self.write_r16_2(x, y, new_n);
    }

    // DEC XY
    // Affect: - - - -
    // CPU Clock: -
    // Bytes: 2
    fn dec_xy(&mut self, x: Register, y: Register) -> () {
        let n = self.read_r16_2(x, y);
        let new_n = n.wrapping_sub(1);
        self.write_r16_2(x, y, new_n);
    }

    // JR PRED, r8
    // Affect: - - - -
    // CPU Clock: 12/8
    // Bytes: 2
    fn jr_pred_r8(&mut self, pred: bool) -> () {
        // relative_addr is signed.
        let relative_addr = self.read_u8_pc();

        if pred {
            // Note that as u16 add 0 to the head, but as relative_addr is signed,
            // we manually add 1 if it means negative value.
            let relative_addr_16 = expand_to_u16_retaining_sign(relative_addr);
            let addr = self.read_r16(Register::PC).wrapping_add(relative_addr_16);
            self.write_r16(Register::PC, addr);
            self.set_proc_clock(12);
        } else {
            self.set_proc_clock(8);
        }
    }

    // SUB X
    // Affect: Z 1 H C
    // CPU Clock: -
    // Bytes: 1
    fn sub_x(&mut self, r: Register) -> () {
        let n = self.read_r8(Register::A);
        let o = self.read_r8(r);
        self.write_r8(Register::A, n.wrapping_sub(o));

        // FIXME: Use 2 complement?
        self.flag_set(FLAG_ZERO, n == o);
        self.flag_set(FLAG_N, true);

        // How about half carry and carry/
    }


    // CP d8
    // Affect: Z, 1, H, C
    // CPU Clock: -
    // Bytes: 1
    fn cp_n(&mut self, n: u8) -> () {
        // This is basically A - n
        let a = self.read_r8(Register::A);

        self.flag_set(FLAG_ZERO, a == n);
        self.flag_set(FLAG_N, true);
        // FIXME: Is this correct?
        self.flag_set(FLAG_HALF_CARRY, (a & 0x0F) < (n & 0x0F));
        self.flag_set(FLAG_CARRY, a < n);
    }

    // actual functions

    // 0x00
    // NOP
    // Affect: - - - -
    // CPU Clock 4
    // Bytes 1
    fn nop(&mut self) -> () {
        self.set_proc_clock(4);
    }

    // 0x03
    // INC BC
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes 2
    fn inc_bc(&mut self) -> () {
        self.inc_xy(Register::B, Register::C);
        self.set_proc_clock(8);
    }

    // 0x04
    // INC B
    // Affect: Z 0 H -
    // CPU Clock 4
    // Bytes 1
    fn inc_b(&mut self) -> () {
        self.inc_x(Register::B);
        self.set_proc_clock(4);
    }


    // 0x05
    // DEC B
    // Affect: Z 1 H -
    // CPU Clock: 4
    // Bytes: 1
    fn dec_b(&mut self) -> () {
        self.dec_x(Register::B);
        self.set_proc_clock(4);
    }

    // 0x06
    // LD B,d8
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 2
    fn ld_b_d8(&mut self) -> () {
        self.ld_x_d8(Register::B);
        self.set_proc_clock(8);
    }

    // 0x0A
    // LD A, (BC)
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes 1
    fn ld_a_addr_bc(&mut self) -> () {
        self.ld_a_addr_xy(Register::B, Register::C);
    }

    // 0x0C
    // INC C
    // Affect: Z 0 H -
    // CPU Clock 4
    // Bytes 1
    fn inc_c(&mut self) -> () {
        self.inc_x(Register::C);
        self.set_proc_clock(4);
    }

    // 0x0D
    // DEC C
    // Affect: Z 1 H -
    // CPU Clock: 4
    // Bytes: 1
    fn dec_c(&mut self) -> () {
        self.dec_x(Register::C);
        self.set_proc_clock(4);
    }

    // 0x0E
    // LD C, d8
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 2
    fn ld_c_d8(&mut self) -> () {
        self.ld_x_d8(Register::C);
        self.set_proc_clock(8);
    }

    // 0x11
    // LD DE, d16
    // Affect: - - - -
    // CPU Clock: 12
    // Bytes: 3
    fn ld_de_d16(&mut self) -> () {
        self.ld_xy_d16(Register::D, Register::E);
        self.set_proc_clock(12);
    }

    // 0x13
    // INC DE
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes 2
    fn inc_de(&mut self) -> () {
        self.inc_xy(Register::D, Register::E);
        self.set_proc_clock(8);
    }

    // 0x14
    // INC D
    // Affect: Z 0 H -
    // CPU Clock 4
    // Bytes 1
    fn inc_d(&mut self) -> () {
        self.inc_x(Register::D);
        self.set_proc_clock(4);
    }

    // 0x15
    // DEC D
    // Affect: Z 1 H -
    // CPU Clock: 4
    // Bytes: 1
    fn dec_d(&mut self) -> () {
        self.dec_x(Register::D);
        self.set_proc_clock(4);
    }

    // 0x16
    // LD D, d8
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 2
    fn ld_d_d8(&mut self) -> () {
        self.ld_x_d8(Register::D);
        self.set_proc_clock(8);
    }

    // 0x17
    // RLA
    // Affect: Z 0 0 C
    // CPU Clock: 4
    // Bytes: 1
    fn rla(&mut self) -> () {
        self.rl_x(Register::A);
        self.set_proc_clock(4);
    }

    // 0x18
    // JR r8
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 2
    fn jr_r8(&mut self) -> () {
        self.jr_pred_r8(true);
    }

    // 0x1A
    // LD A, (DE)
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes 1
    fn ld_a_addr_de(&mut self) -> () {
        self.ld_a_addr_xy(Register::D, Register::E);
        self.set_proc_clock(8);
    }

    // 0x1C
    // INC E
    // Affect: Z 0 H -
    // CPU Clock 4
    // Bytes 1
    fn inc_e(&mut self) -> () {
        self.inc_x(Register::E);
        self.set_proc_clock(4);
    }

    // 0x1D
    // DEC D
    // Affect: Z 1 H -
    // CPU Clock: 4
    // Bytes: 1
    fn dec_e(&mut self) -> () {
        self.dec_x(Register::E);
        self.set_proc_clock(4);
    }

    // 0x1E
    // LD E, d8
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 2
    fn ld_e_d8(&mut self) -> () {
        self.ld_x_d8(Register::E);
        self.set_proc_clock(8);
    }

    // 0x20
    // JR NZ, r8
    // Affect: - - - -
    // CPU Clock: 12/8
    // Bytes: 2
    fn jr_nz_r8(&mut self) -> () {
        let pred = !self.flag_is_set(FLAG_ZERO);
        self.jr_pred_r8(pred);
    }

    // 0x21
    // LD HL, d16
    // Affect: - - - -
    // CPU Clock: 12
    // Bytes: 3
    fn ld_hl_d16(&mut self) -> () {
        self.ld_xy_d16(Register::H, Register::L);
        self.set_proc_clock(12);
    }

    // 0x22
    // LD (HL+),A
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 1
    fn ld_addr_hl_plus_a(&mut self) -> () {
        let hl = self.read_r16_2(Register::H, Register::L);
        self.wb(hl, self.read_r8(Register::A));
        // FIXME: Use wrapping_add or inc_xy
        let nhl = hl + 1;
        self.write_r16_2(Register::H, Register::L, nhl);
        self.set_proc_clock(8);
    }

    // 0x23
    // INC HL
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes 2
    fn inc_hl(&mut self) -> () {
        self.inc_xy(Register::H, Register::L);
        self.set_proc_clock(8);
    }

    // 0x24
    // INC H
    // Affect: Z 0 H -
    // CPU Clock 4
    // Bytes 1
    fn inc_h(&mut self) -> () {
        self.inc_x(Register::H);
        self.set_proc_clock(4);
    }

    // 0x25
    // DEC H
    // Affect: Z 1 H -
    // CPU Clock: 4
    // Bytes: 1
    fn dec_h(&mut self) -> () {
        self.dec_x(Register::H);
        self.set_proc_clock(4);
    }

    // 0x26
    // LD H, d8
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 2
    fn ld_h_d8(&mut self) -> () {
        self.ld_x_d8(Register::H);
        self.set_proc_clock(8);
    }

    // 0x28
    // 0x20
    // JR NZ, r8
    // Affect: - - - -
    // CPU Clock: 12/8
    // Bytes: 2
    fn jr_z_r8(&mut self) -> () {
        let pred = self.flag_is_set(FLAG_ZERO);
        self.jr_pred_r8(pred);
    }

    // 0x2C
    // INC L
    // Affect: Z 0 H -
    // CPU Clock 4
    // Bytes 1
    fn inc_l(&mut self) -> () {
        self.inc_x(Register::L);
        self.set_proc_clock(4);
    }

    // 0x2D
    // DEC L
    // Affect: Z 1 H -
    // CPU Clock: 4
    // Bytes: 1
    fn dec_l(&mut self) -> () {
        self.dec_x(Register::L);
        self.set_proc_clock(4);
    }

    // 0x2E
    // LD L, d8
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 2
    fn ld_l_d8(&mut self) -> () {
        self.ld_x_d8(Register::L);
        self.set_proc_clock(8);
    }

    // 0x31
    // LD SP, d16
    // Affect: - - - -
    // CPU Clock: 12
    // Bytes: 3
    fn ld_sp_d16(&mut self) -> () {
        let nn = self.read_u16_pc();
        self.write_r16(Register::SP, nn);
        self.set_proc_clock(12);
    }

    // 0x32
    // LD (HL-),A
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 1
    fn ld_addr_hl_minus_a(&mut self) -> () {
        let hl = self.read_r16_2(Register::H, Register::L);
        self.wb(hl, self.read_r8(Register::A));
        // FIXME: Use wrapping_sub or dec_xy
        let nhl = hl - 1;
        self.write_r16_2(Register::H, Register::L, nhl);
        self.set_proc_clock(8);
    }

    // 0x34
    // INC A
    // Affect: Z 0 H -
    // CPU Clock 4
    // Bytes 1
    fn inc_a(&mut self) -> () {
        self.inc_x(Register::A);
        self.set_proc_clock(4);
    }

    // 0x3D
    // DEC A
    // Affect: Z 1 H -
    // CPU Clock: 4
    // Bytes: 1
    fn dec_a(&mut self) -> () {
        self.dec_x(Register::A);
        self.set_proc_clock(4);
    }


    // 0x3E
    // LD A,d8
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 2
    fn ld_a_d8(&mut self) -> () {
        self.ld_x_d8(Register::A);
        self.set_proc_clock(8);
    }

    // 0x47
    // LD B, A
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_b_a(&mut self) -> () {
        self.ld_x_y(Register::B, Register::A);
        self.set_proc_clock(4);
    }

    // 0x4F
    // LD C, A
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_c_a(&mut self) -> () {
        self.ld_x_y(Register::C, Register::A);
        self.set_proc_clock(4);
    }

    // 0x57
    // LD D, A
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_d_a(&mut self) -> () {
        self.ld_x_y(Register::D, Register::A);
        self.set_proc_clock(4);
    }

    // 0x5F
    // LD E, A
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_e_a(&mut self) -> () {
        self.ld_x_y(Register::E, Register::A);
        self.set_proc_clock(4);
    }

    // 0x67
    // LD H, A
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_h_a(&mut self) -> () {
        self.ld_x_y(Register::H, Register::A);
        self.set_proc_clock(4);
    }

    // 0x6F
    // LD L, A
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_l_a(&mut self) -> () {
        self.ld_x_y(Register::L, Register::A);
        self.set_proc_clock(4);
    }

    // 0x77
    // LD (HL), A
    // Affect - - - -
    // CPU Clock: 8
    // Bytes: 1
    fn ld_addr_hl_a(&mut self) -> () {
        let addr = self.read_r16_2(Register::H, Register::L);
        self.wb(addr, self.read_r8(Register::A));
        self.set_proc_clock(8);
    }

    // 0x78
    // LD A, B
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_a_b(&mut self) -> () {
        self.ld_x_y(Register::A, Register::B);
        self.set_proc_clock(4);
    }

    // 0x79
    // LD A, C
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_a_c(&mut self) -> () {
        self.ld_x_y(Register::A, Register::C);
        self.set_proc_clock(4);
    }

    // 0x7A
    // LD A, D
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_a_d(&mut self) -> () {
        self.ld_x_y(Register::A, Register::D);
        self.set_proc_clock(4);
    }

    // 0x7B
    // LD A, E
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_a_e(&mut self) -> () {
        self.ld_x_y(Register::A, Register::E);
        self.set_proc_clock(4);
    }

    // 0x7C
    // LD A, H
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_a_h(&mut self) -> () {
        self.ld_x_y(Register::A, Register::H);
        self.set_proc_clock(4);
    }

    // 0x7D
    // LD A, H
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_a_l(&mut self) -> () {
        self.ld_x_y(Register::A, Register::L);
        self.set_proc_clock(4);
    }

    // 0x7F
    // LD A, A
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_a_a(&mut self) -> () {
        self.ld_x_y(Register::A, Register::A);
        self.set_proc_clock(4);
    }

    // 0x80
    // ADD A, B
    // Affect: Z 0 H C
    // CPU Clock: 4
    // Bytes: 1
    fn add_a_b(&mut self) -> () {
        let prev = self.read_r8(Register::A);
        let next = prev.wrapping_add(self.read_r8(Register::B));
        self.write_r8(Register::A, next);

        self.flag_clear();
        self.flag_set(FLAG_ZERO, self.read_r8(Register::A) == 0);
        self.flag_set(FLAG_CARRY, prev > self.read_r8(Register::A));
        // FIXME: How about half carry?

        self.set_proc_clock(4);
    }

    // 0x86
    // ADD A, (HL)
    // Affect: Z 0 H C
    // CPU Clock: 8
    // Bytes: 1
    fn add_addr_hl(&mut self) -> () {
        let prev = self.read_r8(Register::A);
        let addr = self.read_r16_2(Register::H, Register::L);
        let next = prev.wrapping_add(self.rb(addr));
        self.write_r8(Register::A, next);

        self.flag_clear();
        self.flag_set(FLAG_ZERO, self.read_r8(Register::A) == 0);
        self.flag_set(FLAG_CARRY, prev > self.read_r8(Register::A));
        // FIXME: How about half carry?

        self.set_proc_clock(4);
    }

    // 0x90
    // SUB B
    // Affect: Z 1 H C
    // CPU Clock: 4
    // Bytes 1
    fn sub_b(&mut self) -> () {
        self.sub_x(Register::B);
        self.set_proc_clock(4);
    }

    // 0x91
    // SUB C
    // Affect: Z 1 H C
    // CPU Clock: 4
    // Bytes 1
    fn sub_c(&mut self) -> () {
        self.sub_x(Register::C);
        self.set_proc_clock(4);
    }
    // 0x92
    // SUB D
    // Affect: Z 1 H C
    // CPU Clock: 4
    // Bytes 1
    fn sub_d(&mut self) -> () {
        self.sub_x(Register::D);
        self.set_proc_clock(4);
    }
    // 0x93
    // SUB E
    // Affect: Z 1 H C
    // CPU Clock: 4
    // Bytes 1
    fn sub_e(&mut self) -> () {
        self.sub_x(Register::E);
        self.set_proc_clock(4);
    }

    // 0x94
    // SUB H
    // Affect: Z 1 H C
    // CPU Clock: 4
    // Bytes 1
    fn sub_h(&mut self) -> () {
        self.sub_x(Register::H);
        self.set_proc_clock(4);
    }

    // 0x95
    // SUB L
    // Affect: Z 1 H C
    // CPU Clock: 4
    // Bytes 1
    fn sub_l(&mut self) -> () {
        self.sub_x(Register::L);
        self.set_proc_clock(4);
    }

    // 0x97
    // SUB A
    // Affect: Z 1 H C
    // CPU Clock: 4
    // Bytes 1
    fn sub_a(&mut self) -> () {
        self.sub_x(Register::A);
        self.set_proc_clock(4);
    }

    // 0xAF
    // XOR A
    // Affect: Z 0 0 0
    // CPU Clock: 4
    // Bytes: 1
    fn xor_a(&mut self) -> () {
        let prev = self.read_r8(Register::A);
        let next = prev ^ prev;
        self.write_r8(Register::A, next);

        self.flag_clear();
        self.flag_set(FLAG_ZERO, self.read_r8(Register::A) == 0);

        self.set_proc_clock(4);
    }

    // 0xBE
    // CP (HL)
    // Affect: Z 1 H C
    // CPU Clock: 8
    // Bytes: 1
    fn cp_addr_hl(&mut self) -> () {
        let addr = self.read_r16_2(Register::H, Register::L);
        let n = self.rb(addr);
        self.cp_n(n);
        self.set_proc_clock(8);
    }

    // 0xC1
    // POP BC
    // Affect: - - - -
    // CPU Clock: 12
    // Bytes: 1
    fn pop_bc(&mut self) -> () {
        self.pop_xy(Register::B, Register::C);
        self.set_proc_clock(12);
    }

    // 0xC3
    // JP d16
    // Affect: - - - -
    // CPU Clock: 12
    // Bytes: 3
    fn jp_d16(&mut self) -> () {
        let nn = self.read_u16_pc();
        self.write_r16(Register::PC, nn);
        self.set_proc_clock(12);
    }

    // 0xC5
    // PUSH BC
    // Affect: - - - -
    // CPU Clock: 16
    // Bytes: 1
    fn push_bc(&mut self) -> () {
        self.push_xy(Register::B, Register::C);
        self.set_proc_clock(16);
    }

    // 0xC9
    // RET
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 1
    fn ret(&mut self) -> () {
        let addr = self.pop_u16();
        self.write_r16(Register::PC, addr);
        self.set_proc_clock(8);
    }

    // 0xCD
    // CALL a16
    // Affect: - - - -
    // CPU Clock: 12
    // Bytes: 3
    fn call_a16(&mut self) -> () {
        let addr = self.read_u16_pc();
        self.push_u16(self.read_r16(Register::PC));
        self.write_r16(Register::PC, addr);
        self.set_proc_clock(12);
    }

    // 0xE0
    // LDH (n), A (= LD (0xFF00 + n), A)
    // Affect - - - -
    // CPU Clock: 12
    // Bytes: 2
    fn ldh_addr_n_a(&mut self) -> () {
        let n = self.read_u8_pc();

        let addr : u16 = 0xFF00 + n as u16;
        self.wb(addr, self.read_r8(Register::A));
        self.set_proc_clock(12);
    }

    // 0xE2
    // LD (C), A  (= LD (0xFF00 + C), A)
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 1
    fn ldh_addr_c_a(&mut self) -> () {
        let addr : u16 = 0xFF00 + self.read_r8(Register::C) as u16;
        self.wb(addr, self.read_r8(Register::A));
        self.set_proc_clock(8);
    }

    // 0xEA
    // LD (nn), A
    // Affect: - - - -
    // CPU Clock: 16
    // Bytes: 3
    fn ld_addr_d16_a(&mut self) -> () {
        let addr = self.read_u16_pc();
        self.wb(addr, self.read_r8(Register::A));
        self.set_proc_clock(16);
    }

    // 0xF0
    // LDH A, (n) = LD A, ($FF00 + n)
    // Affect: - - - -
    // CPU Clock: 12
    // Bytes: 2
    fn ldh_a_addr_d8(&mut self) -> () {
        let n = self.read_u8_pc();
        let addr : u16 = 0xFF00 + n as u16;
        let val = self.rb(addr);
        self.write_r8(Register::A, val);
        self.set_proc_clock(12);
    }

    // 0xF2
    // LDH A, (C) = LD A, (0xFF00+C)
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 1
    fn ldh_a_addr_c(&mut self) -> () {
        let addr : u16 = 0xFF00 + self.read_r8(Register::C) as u16;
        let val = self.rb(addr);
        self.write_r8(Register::A, val);
        self.set_proc_clock(8);
    }

    // 0xF3
    // DI
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn di(&mut self) -> () {
        // FIXME: Implement here
        eprintln!("DI is not implemented");
        self.set_proc_clock(4);
    }

    // 0xFE
    // CP d16
    // Affect: Z, 1, H, C
    // CPU Clock: 8
    // Bytes: 2
    fn cp_d8(&mut self) -> () {
        let n = self.read_u8_pc();
        self.cp_n(n);
        self.set_proc_clock(8);
    }

    // Prefix CB instructions

    // 0xCB 0x11
    // RL C
    // Affect: Z 0 0 C
    // CPU Clock: 8
    // Bytes: 2
    fn rl_c(&mut self) -> () {
        self.rl_x(Register::C);
        self.set_proc_clock(8);
    }

    // 0xCB 0x7C
    // BIT 7, H
    // Affect: Z 0 1 -
    // CPU Clock: 8
    // Bytes: 2
    fn bit_7_h(&mut self) -> () {
        let s = self.read_r8(Register::H) & (1 << 7) == 0;
        self.flag_set(FLAG_ZERO, s);
        self.flag_set(FLAG_N, false);
        self.flag_set(FLAG_HALF_CARRY, true);

        self.set_proc_clock(8);
    }

    // Memory instructions
    fn rb(&self, addr: u16) -> u8 {
        match addr & 0xF000 {
            0x0000 => {
                if self.read_from_bios && addr < 0x0100 {
                    self.bios[addr as usize]
                } else {
                    // read from cart
                    self.cart[addr as usize]
                }
            },
            0x8000 | 0x9000 => {
                // VRAM
                // 0x8000 - 0x87FF | Tile set #1   0 - 127
                // 0x8800 - 0x8FFF | Tile set #1 128 - 255
                //                 | Tile set #0  -1 - -128
                // 0x9000 - 0x97FF | Tile set #0   0 - 127
                // 0x9800 - 0x9BFF | Tile map #0
                // 0x9C00 - 0x9FFF | Tile map #1
                self.vram[(addr - VRAM_START) as usize]
            },
            0xF000 => {
                match addr & 0x0F00 {
                    0x0F00 => {
                        // zero page or memory-mapped IO
                        if addr >= 0xFF80 {
                            // zero page
                            self.memory_zero[(addr - 0xFF80) as usize]
                        } else {
                            // memory-mapped IO
                            match addr {
                                // TAC
                                0xFF03 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize]
                                },
                                // IF
                                0xFF0F => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize]
                                }
                                // NR 11
                                0xFF11 => {
                                    0
                                },
                                // NR 12
                                0xFF12 => {
                                    0
                                },
                                // NR 13
                                0xFF13 => {
                                    0
                                },
                                // NR 14
                                0xFF14 => {
                                    0
                                },
                                // NR 50
                                0xFF24 => {
                                    0
                                },
                                // NR 51
                                0xFF25 => {
                                    0
                                },
                                // NR 52
                                0xFF26 => {
                                    0
                                },
                                // ?
                                0xFF0C => {
                                    0
                                }
                                // LCDC
                                0xFF40 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize]
                                }
                                // SCY
                                0xFF42 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize]
                                },
                                // LY
                                0xFF44 => {
                                    self.gpu_line
                                },
                                // BGP
                                0xFF47 => {
                                    0
                                },
                                0xFF50 => {
                                    0
                                },
                                _ => {
                                    unimplemented!("Read of Memory-mapped IO ${:04X?} is not implemented", addr);
                                    0
                                }
                            }
                        }
                    }
                    _ => {
                        unimplemented!();
                        0
                    }
                }
            }
            _ => {
                unimplemented!();
                0
            }
        }
    }
    fn rw(&mut self, addr: u16) -> u16 {
        (self.rb(addr) as u16) | ((self.rb(addr+1) as u16) << 8)
    }

    fn wb(&mut self, addr: u16, val: u8) -> () {
        match addr & 0xF000 {
            0x0000 => {
            },
            0x8000 | 0x9000 => {
                // VRAM
                self.vram[(addr - VRAM_START) as usize] = val;
            }
            0xF000 => {
                match addr & 0x0F00 {
                    0x0F00 => {
                        // zero page or memory-mapped IO
                        if addr >= MEMORY_ZERO_START {
                            // zero page
                            self.memory_zero[(addr - MEMORY_ZERO_START) as usize] = val
                        } else {
                            match addr {
                                // TAC
                                0xFF07 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize] = val;
                                },
                                // IF
                                0xFF0F => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize] = val;
                                    eprintln!("Implement clock interrupt");
                                }
                                // NR 11
                                0xFF11 => {
                                },
                                // NR 12
                                0xFF12 => {
                                },
                                // NR 13
                                0xFF13 => {
                                },
                                // NR 14
                                0xFF14 => {
                                },
                                // NR 50
                                0xFF24 => {
                                },
                                // NR 51
                                0xFF25 => {
                                },
                                // NR 52
                                0xFF26 => {
                                },
                                // ?
                                0xFF0C => {
                                },
                                // LCDC
                                0xFF40 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize] = val
                                }
                                // SCY
                                0xFF42 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize] = val
                                },
                                // LY
                                0xFF44 => {
                                },
                                // BGP
                                0xFF47 => {
                                },
                                // ?
                                0xFF50 => {
                                    self.read_from_bios = false;
                                    // self.dump_screen_ppm();
                                    // self.dump_tileset0_ppm();
                                },
                                _ => {
                                    unimplemented!("Write of Memory-mapped IO ${:04X?} is not implemented", addr);
                                }
                            }
                        }
                    }
                    _ => {
                    }
                }
            }
            _ => {
            }
        }
    }

    fn ww(&mut self, addr: u16, val: u16) -> () {
        unimplemented!("ww");
    }

    // dispatch
    pub fn new() -> SystemOnChip {
        SystemOnChip {
            regs: Regs::new(),
            read_from_bios: true,
            vram: [0; VRAM_SIZE as usize],
            mapped_io: [0; MAPPED_IO_SIZE as usize],
            memory_zero: [0; MEMORY_ZERO_SIZE as usize],
            cart: Vec::new(),
            bios: [0; 256], // 0 is nop,
            // GPU
            gpu_screen: [0; 160 * 144],
            gpu_mode: GpuMode::ScanlineAccessingOAM,
            gpu_mode_clock: 0,
            gpu_line: 0,
        }
    }

    pub fn load_cart(&mut self, cart: &Vec<u8>) {
        self.cart.clone_from(&cart);
    }

    pub fn load_bios(&mut self, bios: &Vec<u8>) {
        if bios.len() != self.bios.len() {
            panic!();
        }

        for i in 0..self.bios.len() {
            self.bios[i] = bios[i]
        }
    }

    fn dispatch(&mut self) -> () {
        assert_eq!(self.get_proc_clock(), 0);

        let pc = self.read_r16(Register::PC);
        let op = self.read_u8_pc();

        // eprintln!("${:04X?}", pc);
        // self.dump_registers();

        match op {
            0x00 => self.nop(),
            0x03 => self.inc_bc(),
            0x04 => self.inc_b(),
            0x05 => self.dec_b(),
            0x06 => self.ld_b_d8(),
            0x0A => self.ld_a_addr_bc(),
            0x0C => self.inc_c(),
            0x0D => self.dec_c(),
            0x0E => self.ld_c_d8(),
            0x11 => self.ld_de_d16(),
            0x13 => self.inc_de(),
            0x14 => self.inc_d(),
            0x15 => self.dec_d(),
            0x16 => self.ld_d_d8(),
            0x17 => self.rla(),
            0x18 => self.jr_r8(),
            0x1A => self.ld_a_addr_de(),
            0x1C => self.inc_e(),
            0x1D => self.dec_e(),
            0x1E => self.ld_e_d8(),
            0x20 => self.jr_nz_r8(),
            0x21 => self.ld_hl_d16(),
            0x22 => self.ld_addr_hl_plus_a(),
            0x23 => self.inc_hl(),
            0x24 => self.inc_h(),
            0x25 => self.dec_h(),
            0x26 => self.ld_h_d8(),
            0x28 => self.jr_z_r8(),
            0x2C => self.inc_l(),
            0x2D => self.dec_l(),
            0x2E => self.ld_l_d8(),
            0x31 => self.ld_sp_d16(),
            0x32 => self.ld_addr_hl_minus_a(),
            0x34 => self.inc_a(),
            0x3D => self.dec_a(),
            0x3E => self.ld_a_d8(),
            0x47 => self.ld_b_a(),
            0x4F => self.ld_c_a(),
            0x57 => self.ld_d_a(),
            0x5F => self.ld_e_a(),
            0x67 => self.ld_h_a(),
            0x6F => self.ld_l_a(),
            0x77 => self.ld_addr_hl_a(),
            0x78 => self.ld_a_b(),
            0x79 => self.ld_a_c(),
            0x7A => self.ld_a_d(),
            0x7B => self.ld_a_e(),
            0x7C => self.ld_a_h(),
            0x7D => self.ld_a_l(),
            0x7F => self.ld_a_a(),
            0x80 => self.add_a_b(),
            0x86 => self.add_addr_hl(),
            0x90 => self.sub_b(),
            0x91 => self.sub_c(),
            0x92 => self.sub_d(),
            0x93 => self.sub_e(),
            0x94 => self.sub_h(),
            0x95 => self.sub_l(),
            0x97 => self.sub_a(),
            0xAF => self.xor_a(),
            0xBE => self.cp_addr_hl(),
            0xC1 => self.pop_bc(),
            0xC3 => self.jp_d16(),
            0xC5 => self.push_bc(),
            0xC9 => self.ret(),
            0xCD => self.call_a16(),
            0xE0 => self.ldh_addr_n_a(),
            0xE2 => self.ldh_addr_c_a(),
            0xEA => self.ld_addr_d16_a(),
            0xF0 => self.ldh_a_addr_d8(),
            0xF2 => self.ldh_a_addr_c(),
            0xF3 => self.di(),
            0xFE => self.cp_d8(),
            // Prefix CB
            0xCB => {
                let pc = self.read_r16(Register::PC);
                let op = self.read_u8_pc();
                match op {
                    0x7C => self.bit_7_h(),
                    0x11 => self.rl_c(),
                    _ => {
                        unimplemented!("op 0xCB 0x{:02X?} at 0x{:04X?}", op, pc);
                    }
                }
            }
            _ => {
                unimplemented!("op 0x{:02X?} at 0x{:04X?}", op, pc);
            }
        }
        if self.get_proc_clock() == 0 {
            unimplemented!("op 0x{:02X?} at 0x{:04X?} doesn't set lt.", op, pc);
        }
        self.regs.t += self.regs.lt as u32;
    }

    fn gpu_render_line(&mut self, line: u8) {
        // 0x8000 - 0x87FF | Tile set #1   0 - 127
        // 0x8800 - 0x8FFF | Tile set #1 128 - 255
        //                 | Tile set #0  -1 - -128
        // 0x9000 - 0x97FF | Tile set #0   0 - 127
        // 0x9800 - 0x9BFF | Tile map #0
        // 0x9C00 - 0x9FFF | Tile map #1

        // Screen size is 160x144.
        // Buffer size is 256x256.
        // Tile size is 8x8, so buffer has 32x32 tiles.

        // FF40
        //   Bit 4 - BG & Window Tile Data Select   (0=8800-97FF, 1=8000-8FFF)
        //   Bit 3 - BG Tile Map Display Select     (0=9800-9BFF, 1=9C00-9FFF)

        let is_tile_set_0 = (self.rb(0xFF40) & (1 << 4)) == 0;
        let is_tile_map_0 = (self.rb(0xFF40) & (1 << 3)) == 0;

        let tile_set_addr = match is_tile_set_0 {
            true => 0x9000 as u16,
            false => 0x8000 as u16
        };

        let tile_map_addr = match is_tile_map_0 {
            true => 0x9800 as u16,
            false => 0x9C00 as u16
        };

        // FIXME: use scx, scy.
        let screen_y = line;
        let scroll_y = self.rb(0xFF42);
        let scroll_x = 0 as u8;

        let buffer_y = line + scroll_y;

        for screen_x in 0..160 {
            let buffer_x = scroll_x + screen_x;

            let tile_y = buffer_y / 8;
            let tile_x = buffer_x / 8;
            let tile_id_addr = tile_map_addr + (tile_y as u16) * 32 + (tile_x as u16);
            assert!(
                if is_tile_map_0 {
                    0x9800 <= tile_id_addr && tile_id_addr <= 0x9BFF
                } else {
                    0x9C00 <= tile_id_addr && tile_id_addr <= 0x9FFF
                });

            let tile_id = self.rb(tile_id_addr);

            let ly = buffer_y % 8;
            let lx = buffer_x % 8;

            // Signed case is also covered by wrapping_add.
            let tile_id_u16 = match is_tile_set_0 {
                true => expand_to_u16_retaining_sign(tile_id),
                false => tile_id as u16,
            };
            // 16 bytes per 1 tile.
            // FIXME: Can we use wrapping_mul?
            let mut tile_addr_offset = 0 as u16;
            for _ in 0..16 {
                tile_addr_offset = tile_addr_offset.wrapping_add(tile_id_u16);
            }
            let tile_addr = tile_set_addr.wrapping_add(tile_addr_offset);
            assert!(0x8000 <= tile_addr && tile_addr <= 0x97FF);

            // 2 bytes consist of 1 line.
            let line_addr1 = tile_addr + (2 * ly as u16);
            let line_addr2 = line_addr1 + 1;
            assert!(
                if is_tile_set_0 {
                    0x8800 <= line_addr1 && line_addr1 <= 0x97FF &&
                    0x8800 <= line_addr2 && line_addr2 <= 0x97FF
                } else {
                    0x8000 <= line_addr1 && line_addr1 <= 0x8FFF &&
                    0x8000 <= line_addr2 && line_addr2 <= 0x8FFF
                });

            let line_val1 = self.rb(line_addr1);
            let line_val2 = self.rb(line_addr2);
            let rlx = 7 - lx;
            let val = ((((line_val1 & (1 << rlx)) >> rlx) << 1) + ((line_val2 & (1 << rlx)) >> rlx)) as u8;
            self.gpu_screen[(160 * (screen_y as u16) + (screen_x as u16)) as usize] = val;
        }
    }

    fn gpu_step(&mut self, c: u8) {
        self.gpu_mode_clock += c as u16;

        // (ScanlineAccessingOAM
        //    => ScanlineAccessingVRAM
        //    => HorizontalBlank) * 143
        // => VerticalBlank

        // ScanlineAccessingOAM  -> 80 cycles
        // ScanlineAccessingVRAM -> 172 cycles
        // HorizontalBlank       -> 204 cycles
        // VerticalBlank         -> 4560 cycles
        match self.gpu_mode {
            GpuMode::ScanlineAccessingOAM => {
                if self.gpu_mode_clock >= 80 {
                    self.gpu_mode_clock -= 80;
                    self.gpu_mode = GpuMode::ScanlineAccessingVRAM;
                }
            }
            GpuMode::ScanlineAccessingVRAM => {
                if self.gpu_mode_clock >= 172 {
                    self.gpu_mode_clock -= 172;
                    self.gpu_mode = GpuMode::HorizontalBlank;
                    self.gpu_render_line(self.gpu_line);
                }
            }
            GpuMode::HorizontalBlank => {
                if self.gpu_mode_clock >= 204 {
                    self.gpu_mode_clock -= 204;
                    self.gpu_line += 1;

                    if self.gpu_line == 144 {
                        // Go to VBlank
                        self.gpu_mode = GpuMode::VerticalBlank;
                    } else {
                        self.gpu_mode = GpuMode::ScanlineAccessingOAM;
                    }
                }
            }
            // 4560 cycles for 10 lines.
            GpuMode::VerticalBlank => {
                if self.gpu_mode_clock >= 456 {
                    self.gpu_mode_clock -= 456;
                    self.gpu_line += 1;

                    // 154 = 143 + 10?
                    if self.gpu_line >= 154 {
                        self.gpu_mode = GpuMode::ScanlineAccessingOAM;
                        self.gpu_line = 0;
                    }
                }
            }
        }
    }

    pub fn step(&mut self) -> u8 {
        self.dispatch();

        let cyclespent = self.get_proc_clock();
        self.set_proc_clock(0);

        self.gpu_step(cyclespent);

        cyclespent
    }

    pub fn step_seconds(&mut self, seconds : f64) -> () {
        // CPU is 4.19MHz
        let cycles = (seconds * 41943040.0) as u64;
        let mut spent_cycle = 0 as u64;
        while spent_cycle < cycles {
            spent_cycle += self.step() as u64;
        }
    }

    pub fn screen(&mut self) -> [u8; 160 * 144] {
        self.gpu_screen
    }

    // debug functions
    fn dump_registers(&self) -> () {
        // A, B, C, D, E, H, L, F, PC, SP, LT

        eprintln!("A: 0x{:02X?}", self.read_r8(Register::A));
        eprintln!("B: 0x{:02X?}", self.read_r8(Register::B));
        eprintln!("C: 0x{:02X?}", self.read_r8(Register::C));
        eprintln!("D: 0x{:02X?}", self.read_r8(Register::D));
        eprintln!("E: 0x{:02X?}", self.read_r8(Register::E));
        eprintln!("H: 0x{:02X?}", self.read_r8(Register::H));
        eprintln!("L: 0x{:02X?}", self.read_r8(Register::L));
        eprintln!("PC: 0x{:02X?}", self.read_r16(Register::PC));
        eprintln!("SP: 0x{:02X?}", self.read_r16(Register::SP));
    }

    fn dump_screen(&self) -> () {
        for y in 0..144 {
            for x in 0..160 {
                let v = self.gpu_screen[160 * y + x];
                let c = match v {
                    0 => ' ',
                    1 => '.',
                    2 => '*',
                    3 => 'X',
                    _ => '?'
                };
                eprint!("{}", c);
            }
            eprintln!("");
        }
    }

    fn dump_screen_ppm(&self) -> () {
        use std::fs::File;
        use std::io::{BufWriter, Write};

        let mut f = BufWriter::new(File::create("./screen.ppm").unwrap());

        let header = "P3\n160 144\n255\n";
        f.write(header.as_bytes()).unwrap();

        for y in 0..144 {
            for x in 0..160 {
                let v = self.gpu_screen[160 * y + x];
                let c = match v {
                    0 => "255 255 255",
                    1 => "170 170 170",
                    2 => "85 85 85",
                    3 => "0 0 0",
                    _ => "0 0 0"
                };
                f.write(c.as_bytes()).unwrap();
                f.write("\n".as_bytes()).unwrap();
            }
        }
    }

    fn dump_tileset0_ppm(&self) -> () {
        use std::fs::File;
        use std::io::{BufWriter, Write};

        let mut buffer = [0 as u8; 128*128];
        for ty in 0..16 {
            for tx in 0..16 {
                let tile_addr = 0x8000 + 16 * (16 * ty + tx);
                for y in 0..8 {
                    let line_addr1 = tile_addr + 2 * y;
                    let line_addr2 = line_addr1 + 1;

                    let line_val1 = self.rb(line_addr1);
                    let line_val2 = self.rb(line_addr2);

                    for x in 0..8 {
                        let rlx = 7 - x;
                        let val = ((((line_val1 & (1 << rlx)) >> rlx) << 1) + ((line_val2 & (1 << rlx)) >> rlx)) as u8;
                        let sy = 8 * ty + y;
                        let sx = 8 * tx + x;
                        buffer[(128 * sy + sx) as usize] = val;
                    }
                }
            }
        }
        let mut f = BufWriter::new(File::create("./tileset.ppm").unwrap());

        let header = "P3\n128 128\n255\n";
        f.write(header.as_bytes()).unwrap();

        for y in 0..128 {
            for x in 0..128 {
                let v = buffer[128 * y + x];
                let c = match v {
                    0 => "255 255 255",
                    1 => "170 170 170",
                    2 => "85 85 85",
                    3 => "0 0 0",
                    _ => "0 0 0"
                };
                f.write(c.as_bytes()).unwrap();
                f.write("\n".as_bytes()).unwrap();
            }
        }
    }
}
