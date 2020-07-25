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

#[derive(Debug, PartialEq, Clone, Copy)]
struct InterruptFlag {
    transition: bool,
    serial_transfer: bool,
    timer_overflow: bool,
    lcdc: bool,
    vblank: bool
}

impl InterruptFlag {
    pub fn new() -> InterruptFlag {
        InterruptFlag {
            transition: false,
            serial_transfer: false,
            timer_overflow: false,
            lcdc: false,
            vblank: false
        }
    }
    pub fn write_u8(&mut self, val: u8) -> () {
        // Bit 4: Transition from High to Low of Pin number P10-P13.
        // Bit 3: Serial I/O transfer complete
        // Bit 2: Timer Overflow
        // Bit 1: LCDC (see STAT)
        // Bit 0: V-Blank
        self.transition      = (val & (1 << 4)) != 0;
        self.serial_transfer = (val & (1 << 3)) != 0;
        self.timer_overflow  = (val & (1 << 2)) != 0;
        self.lcdc            = (val & (1 << 1)) != 0;
        self.vblank          = (val & (1 << 0)) != 0;
    }

    pub fn read_u8(&self) -> u8 {
        // Bit 4: Transition from High to Low of Pin number P10-P13.
        // Bit 3: Serial I/O transfer complete
        // Bit 2: Timer Overflow
        // Bit 1: LCDC (see STAT)
        // Bit 0: V-Blank

        let mut val = 0;
        if self.transition {
            val |= 1 << 4;
        }
        if self.serial_transfer {
            val |= 1 << 3;
        }
        if self.timer_overflow {
            val |= 1 << 2;
        }
        if self.lcdc {
            val |= 1 << 1;
        }
        if self.vblank {
            val |= 1 << 0;
        }
        val
    }
    pub fn reset(&mut self) -> () {
        self.write_u8(0);
    }

    pub fn or(&mut self, other: InterruptFlag) -> () {
        self.write_u8(self.read_u8() | other.read_u8());
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
struct Joypad {
    a: bool,
    b: bool,
    left: bool,
    right: bool,
    up: bool,
    down: bool,
    start: bool,
    select: bool,
}

impl Joypad {
    pub fn new() -> Joypad {
        Joypad {
            a: false,
            b: false,
            left: false,
            right: false,
            up: false,
            down: false,
            start: false,
            select: false,
        }
    }
}

const VRAM_START : u16 = 0x8000;
const VRAM_END : u16 = 0x9FFF;
const INTERNAL_RAM_START : u16 = 0xC000;
const INTERNAL_RAM_END : u16 = 0xDFFF;
const OAM_START : u16 = 0xFE00;
const OAM_END : u16 = 0xFE9F;
const MAPPED_IO_START: u16 = 0xFF00;
const MAPPED_IO_END : u16 = 0xFF79;
const MEMORY_ZERO_START : u16 = 0xFF80;
const MEMORY_ZERO_END : u16 = 0xFFFF;

const VRAM_SIZE : u16 = VRAM_END - VRAM_START + 1;
const INTERNAL_RAM_SIZE : u16 = INTERNAL_RAM_END - INTERNAL_RAM_START + 1;
const MAPPED_IO_SIZE : u16 = MAPPED_IO_END - MAPPED_IO_START + 1;
const MEMORY_ZERO_SIZE : u16 = MEMORY_ZERO_END - MEMORY_ZERO_START + 1;
const OAM_SIZE : u16 = OAM_END - OAM_START + 1 ;

pub struct SystemOnChip {
    regs: Regs,
    // Between reset and the first read from 0x0100, then
    // 0x0000 - 0x0100 is mapped to bios.
    pub read_from_bios: bool,

    global_interruption_enabled: bool, // used by di, ei
    interruption_enabled: InterruptFlag,
    interruption_occurred: InterruptFlag,
    interruption_occurred_in_this_step: InterruptFlag,
    joypad: Joypad,

    // memory
    // 0x8000 - 0x9FFF
    vram: [u8; VRAM_SIZE as usize],
    // 0xC000 - 0xDFFF
    internal_ram: [u8; INTERNAL_RAM_SIZE as usize],
    // 0xFE00 - 0xFEA0
    oam: [u8; OAM_SIZE as usize],
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
    // CPU Clock: 12
    // Bytes: 3
    fn ld_xy_d16(&mut self, x: Register, y: Register) -> () {
        let high = self.read_u8_pc();
        let low = self.read_u8_pc();

        // FIXME: little endian?
        self.write_r8(y, high);
        self.write_r8(x, low);
        self.set_proc_clock(12);
    }

    // LD X, Y
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ld_x_y(&mut self, x: Register, y: Register) -> () {
        self.write_r8(x, self.read_r8(y));
        self.set_proc_clock(4);
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

    // SLA X
    // Affect: Z 0 0 C
    // CPU Clock: -
    // Bytes: 2
    fn sla_x(&mut self, x: Register) -> () {
        let prev = self.read_r8(x);
        let next = prev << 1;
        let has_carry = (prev & (1 << 7)) != 0;

        self.flag_set(FLAG_ZERO, next == 0);
        self.flag_set(FLAG_N, false);
        self.flag_set(FLAG_HALF_CARRY, false);
        self.flag_set(FLAG_CARRY, has_carry);

        self.write_r8(x, next);
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
    // CPU Clock: 4
    // Bytes: 1
    fn inc_x(&mut self, x: Register) -> () {
        let n = self.read_r8(x);

        self.flag_set(FLAG_ZERO, n == 0xFF);
        self.flag_set(FLAG_N, false);
        // 1 if carry from bit 3 == bit 0 ~ bit 3 is 1.
        self.flag_set(FLAG_HALF_CARRY, (n & 0x0F) == 0x0F);

        self.write_r8(x, n.wrapping_add(1));
        self.set_proc_clock(4);
    }

    // DEC X
    // Affect: Z 1 H -
    // CPU Clock: 4
    // Bytes: 1
    fn dec_x(&mut self, x: Register) -> () {
        let n = self.read_r8(x);

        self.flag_set(FLAG_ZERO, n == 1);
        self.flag_set(FLAG_N, true);
        // 1 if borrow from bit 4 == bit 0 ~ bit 3 is 0.
        self.flag_set(FLAG_HALF_CARRY, (n & 0x0F) == 0);

        self.write_r8(x, n.wrapping_sub(1));
        self.set_proc_clock(4);
    }

    // INC XY
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 2
    fn inc_xy(&mut self, x: Register, y: Register) -> () {
        let n = self.read_r16_2(x, y);
        let new_n = n.wrapping_add(1);
        self.write_r16_2(x, y, new_n);
        self.set_proc_clock(8);
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
    // CPU Clock: 4
    // Bytes: 1
    fn sub_x(&mut self, r: Register) -> () {
        let n = self.read_r8(Register::A);
        let o = self.read_r8(r);
        self.write_r8(Register::A, n.wrapping_sub(o));

        // FIXME: Use 2 complement?
        self.flag_set(FLAG_ZERO, n == o);
        self.flag_set(FLAG_N, true);

        // FIXME: How about half carry and carry?

        self.set_proc_clock(4);
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

    // SWAP x
    // Affect: Z 0 0 0
    // CPU Clock: 8
    // Bytes: 1
    fn swap_x(&mut self, r: Register) -> () {
        let prev = self.read_r8(r);
        let next = ((prev << 4) & 0xF0)| ((prev >> 4) & 0x0F);
        self.write_r8(r, next);

        self.flag_clear();
        self.flag_set(FLAG_ZERO, prev == 0);
        self.set_proc_clock(8);
    }

    // OR x
    // Affect: Z 0 0 0
    // CPU Clock: 8
    // Bytes: 1
    fn or_x(&mut self, r: Register) -> () {
        let prev_a = self.read_r8(Register::A);
        let app = self.read_r8(r);
        let res = prev_a | app;
        self.write_r8(Register::A, res);

        self.flag_clear();
        self.flag_set(FLAG_ZERO, res == 0);
        self.set_proc_clock(4);
    }

    // AND x
    // Affect: Z 0 0 0
    // CPU Clock: 8
    // Bytes: 1
    fn and_x(&mut self, r: Register) -> () {
        let prev_a = self.read_r8(Register::A);
        let app = self.read_r8(r);
        let res = prev_a & app;
        self.write_r8(Register::A, res);

        self.flag_clear();
        self.flag_set(FLAG_ZERO, res == 0);
        self.flag_set(FLAG_HALF_CARRY, true);
        self.set_proc_clock(4);
    }

    // BIT n, x
    // Affect: Z 0 1 -
    // CPU Clock: 8
    // Bytes: 2
    fn bit_n_x(&mut self, n : u8, r: Register) -> () {
        let s = self.read_r8(r) & (1 << n) == 0;
        self.flag_set(FLAG_ZERO, s);
        self.flag_set(FLAG_N, false);
        self.flag_set(FLAG_HALF_CARRY, true);
        self.set_proc_clock(8);
    }

    // ADD WX YZ
    // Affect: - 0 H C
    // CPU Clock: 8
    // Bytes: 1
    fn add_wx_yz(&mut self, w: Register, x: Register, y: Register, z: Register) -> () {
        let prev = self.read_r16_2(w, x);
        let n = self.read_r16_2(y, z);

        let next = prev.wrapping_add(n);
        self.write_r16_2(w, x, next);
        // FIXME: How about half carry and carry?

        self.set_proc_clock(8);
    }

    // actual functions

    // 0x00
    // NOP
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes 1
    fn nop(&mut self) -> () {
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
        self.set_proc_clock(8);
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

    // 0x19
    // ADD HL, DE
    // Affect: - 0 H C
    // CPU Clock: 8
    // Bytes: 1
    fn add_hl_de(&mut self) -> () {
        self.add_wx_yz(Register::H, Register::L, Register::D, Register::E);
        self.set_proc_clock(8);
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

    // 0x22
    // LD (HL+),A
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 1
    fn ld_addr_hl_plus_a(&mut self) -> () {
        let hl = self.read_r16_2(Register::H, Register::L);
        self.wb(hl, self.read_r8(Register::A));
        let nhl = hl.wrapping_add(1);
        self.write_r16_2(Register::H, Register::L, nhl);
        self.set_proc_clock(8);
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

    // 0x2A
    // LD A, (HL+)
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 1
    fn ld_a_addr_hl_plus(&mut self) -> () {
        let hl = self.read_r16_2(Register::H, Register::L);
        self.write_r8(Register::A, self.rb(hl));
        let nhl = hl.wrapping_add(1);
        self.write_r16_2(Register::H, Register::L, nhl);
        self.set_proc_clock(8);
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

    // 0x2F
    // CPL
    // Affect - 1 1 -
    // CPU Clock: 4
    // Bytes: 1
    fn cpl(&mut self) -> () {
        let prev = self.read_r8(Register::A);
        let val = !prev;
        self.write_r8(Register::A, val);

        self.flag_set(FLAG_N, true);
        self.flag_set(FLAG_HALF_CARRY, true);

        self.set_proc_clock(4);
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

    // 0x35
    // DEC (HL)
    // Affect: Z 1 H -
    // CPU Clock: 12
    // Bytes: 1
    fn dec_addr_hl(&mut self) -> () {
        let addr = self.read_r16_2(Register::H, Register::L);
        let prev = self.rb(addr);
        let next = prev.wrapping_sub(1);

        // FIXME:
        self.flag_set(FLAG_ZERO, next == 0);
        self.flag_set(FLAG_N, true);
        self.flag_set(FLAG_HALF_CARRY, (prev & (1 << 4)) != 0 && (next & (1 << 4) == 0));

        self.set_proc_clock(12);
    }

    // 0x36
    // LD (HL), d8
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 2
    fn ld_addr_hl_d8(&mut self) -> () {
        let hl = self.read_r16_2(Register::H, Register::L);
        let n = self.read_u8_pc();
        self.wb(hl, n);
        self.set_proc_clock(8);
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

    // 0x70
    // LD (HL), B
    // Affect - - - -
    // CPU Clock: 8
    // Bytes: 1
    fn ld_addr_hl_b(&mut self) -> () {
        let addr = self.read_r16_2(Register::H, Register::L);
        self.wb(addr, self.read_r8(Register::B));
        self.set_proc_clock(8);
    }

    // 0x71
    // LD (HL), C
    // Affect - - - -
    // CPU Clock: 8
    // Bytes: 1
    fn ld_addr_hl_c(&mut self) -> () {
        let addr = self.read_r16_2(Register::H, Register::L);
        self.wb(addr, self.read_r8(Register::C));
        self.set_proc_clock(8);
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

    // 0x1A
    // LD A, (HL)
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes 1
    fn ld_a_addr_hl(&mut self) -> () {
        self.ld_a_addr_xy(Register::H, Register::L);
        self.set_proc_clock(8);
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

    // 0xB0
    // OR B
    // Affect: Z 0 0 0
    // CPU Clock: 4
    // Bytes: 1
    fn or_b(&mut self) -> () {
        self.or_x(Register::B);
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

    // 0xC2
    // JP NZ, d16
    // Affect: - - - -
    // CPU Clock: 16/12
    // Bytes: 3
    fn jp_nz_d16(&mut self) -> () {
        let addr = self.read_u16_pc();
        let jump = !self.flag_is_set(FLAG_ZERO);

        if jump {
            self.write_r16(Register::PC, addr);
            self.set_proc_clock(16);
        } else {
            self.set_proc_clock(12);
        }
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

    // 0xCA
    // JP Z, d16
    // Affect: - - - -
    // CPU Clock: 16/12
    // Bytes: 3
    fn jp_z_d16(&mut self) -> () {
        let addr = self.read_u16_pc();
        let jump = self.flag_is_set(FLAG_ZERO);

        if jump {
            self.write_r16(Register::PC, addr);
            self.set_proc_clock(16);
        } else {
            self.set_proc_clock(12);
        }
    }

    // 0xC6
    // ADD A, d8
    // Affect: Z 0 H C
    // CPU Clock: 8
    // Bytes: 2
    fn add_a_d8(&mut self) -> () {
        let prev = self.read_r8(Register::A);
        let n = self.read_u8_pc();
        let next = prev.wrapping_add(n);
        self.write_r8(Register::A, next);

        self.flag_clear();
        self.flag_set(FLAG_ZERO, self.read_r8(Register::A) == 0);
        self.flag_set(FLAG_CARRY, prev > self.read_r8(Register::A));
        // FIXME: How about half carry?

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

    // 0xD1
    // POP DE
    // Affect: - - - -
    // CPU Clock: 12
    // Bytes: 1
    fn pop_de(&mut self) -> () {
        self.pop_xy(Register::D, Register::E);
        self.set_proc_clock(12);
    }

    // 0xD5
    // PUSH DE
    // Affect: - - - -
    // CPU Clock: 16
    // Bytes: 1
    fn push_de(&mut self) -> () {
        self.push_xy(Register::D, Register::E);
        self.set_proc_clock(16);
    }

    // 0xD9
    // RETI
    // Affect: - - - -
    // CPU Clock: 8
    // Bytes: 1
    fn reti(&mut self) -> () {
        let addr = self.pop_u16();
        self.write_r16(Register::PC, addr);
        self.global_interruption_enabled = true;
        self.set_proc_clock(8);
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

    // 0xE1
    // POP HL
    // Affect: - - - -
    // CPU Clock: 12
    // Bytes: 1
    fn pop_hl(&mut self) -> () {
        self.pop_xy(Register::H, Register::L);
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

    // 0xE5
    // PUSH HL
    // Affect: - - - -
    // CPU Clock: 16
    // Bytes: 1
    fn push_hl(&mut self) -> () {
        self.push_xy(Register::H, Register::L);
        self.set_proc_clock(16);
    }

    // 0xE6
    // AND d8
    // Affect: Z 0 1 0
    // CPU Clock: 8
    // Bytes: 2
    fn and_d8(&mut self) -> () {
        let n = self.read_u8_pc();
        let prev = self.read_r8(Register::A);
        let next = prev & n;
        self.write_r8(Register::A, next);

        self.flag_clear();
        self.flag_set(FLAG_ZERO, next == 0);
        self.flag_set(FLAG_N, false);
        self.flag_set(FLAG_HALF_CARRY, true);
        self.flag_set(FLAG_CARRY, false);

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

    // 0xF1
    // POP AF
    // Affect: - - - -
    // CPU Clock: 12
    // Bytes: 1
    fn pop_af(&mut self) -> () {
        self.pop_xy(Register::A, Register::F);
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
        // eprintln!("DI is not implemented correctly, it should disable interruption after the next instruction is executed");
        self.global_interruption_enabled = false;
        self.set_proc_clock(4);
    }

    // 0xF5
    // PUSH AF
    // Affect: - - - -
    // CPU Clock: 16
    // Bytes: 1
    fn push_af(&mut self) -> () {
        self.push_xy(Register::A, Register::F);
        self.set_proc_clock(16);
    }

    // 0xFA
    // LD A, (nn)
    // Affect: - - - -
    // CPU Clock: 16
    // Bytes: 3
    fn ld_a_addr_d16(&mut self) -> () {
        let addr = self.read_u16_pc();
        let valu = self.rb(addr);
        self.write_r8(Register::A, valu);
        self.set_proc_clock(16);
    }

    // 0xFB
    // EI
    // Affect: - - - -
    // CPU Clock: 4
    // Bytes: 1
    fn ei(&mut self) -> () {
        // eprintln!("EI is not implemented correctly, it should enable interruption after the next instruction is executed");
        self.global_interruption_enabled = true;
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
    // BIT functions are not listed here.

    // 0xCB 0x11
    // RL C
    // Affect: Z 0 0 C
    // CPU Clock: 8
    // Bytes: 2
    fn rl_c(&mut self) -> () {
        self.rl_x(Register::C);
        self.set_proc_clock(8);
    }

    // 0xCB 0x23
    // SLA E
    // Affect: Z 0 0 C
    // CPU Clock: 8
    // Bytes: 2
    fn sla_e(&mut self) -> () {
        self.sla_x(Register::E);
        self.set_proc_clock(8);
    }

    // 0xCB 0x27
    // SLA A
    // Affect: Z 0 0 C
    // CPU Clock: 8
    // Bytes: 2
    fn sla_a(&mut self) -> () {
        self.sla_x(Register::A);
        self.set_proc_clock(8);
    }

    // 0xCB 0x37
    // SWAP A
    // Affect: Z 0 0 0
    // CPU Clock: 8
    // Bytes: 1
    fn swap_a(&mut self) -> () {
        self.swap_x(Register::A);
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
            0xC000 | 0xD000 => {
                // Internal RAM
                self.internal_ram[(addr - INTERNAL_RAM_START) as usize]
            },
            0xF000 => {
                match addr & 0x0F00 {
                    0x0F00 => {
                        // zero page or memory-mapped IO
                        if addr == 0xFFFF {
                            self.interruption_enabled.read_u8()
                        } else if addr >= 0xFF80 {
                            // zero page
                            self.memory_zero[(addr - 0xFF80) as usize]
                        } else {
                            // memory-mapped IO
                            match addr {
                                // P1
                                0xFF00 => {
                                    let setting = self.mapped_io[(addr - MAPPED_IO_START) as usize];
                                    let p14 = (setting & (1 << 4)) != 0;
                                    let p15 = (setting & (1 << 5)) != 0;

                                    if p14 {
                                        let p10_bit = if self.joypad.a { 0 } else { 1 };
                                        let p11_bit = if self.joypad.b { 0 } else { 1 };
                                        let p12_bit = if self.joypad.select { 0 } else { 1 };
                                        let p13_bit = if self.joypad.start { 0 } else { 1 };

                                        p10_bit | (p11_bit << 1) | (p12_bit << 2) | (p13_bit << 3)
                                    } else if p15 {
                                        let p10_bit = if self.joypad.right { 0 } else { 1 };
                                        let p11_bit = if self.joypad.left { 0 } else { 1 };
                                        let p12_bit = if self.joypad.up { 0 } else { 1 };
                                        let p13_bit = if self.joypad.down { 0 } else { 1 };

                                        p10_bit | (p11_bit << 1) | (p12_bit << 2) | (p13_bit << 3)
                                    } else {
                                        0x0F
                                    }
                                },
                                // TAC
                                0xFF03 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize]
                                },
                                // IF
                                0xFF0F => {
                                    self.interruption_occurred.read_u8()
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
                                },
                                // LCDC
                                0xFF40 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize]
                                },
                                // STAT
                                0xFF41 => {
                                    // Bit 6 = LYC == LY
                                    // Bit 5 = Mode 10
                                    // Bit 4 = Mode 01
                                    // Bit 3 = Mode 00
                                    // Bit 2 = LYC == LCDC LY
                                    // Bit 1-0 = Mode flag
                                    // 00 = self.gpu_mode == GpuMode::HorizontalBlank
                                    // 01 = self.gpu_mode == GpuMode::VerticalBlank
                                    // 10 = self.gpu_mode == GpuMode::ScanlineAccessingOAM
                                    // 11 = self.gpu_mode == GpuMode::ScanlineAccessingVRAM

                                    // FIXME: Implement all flags
                                    // eprintln!("Implement read of STAT");

                                    let mode_flag = match self.gpu_mode {
                                        GpuMode::ScanlineAccessingOAM => {
                                            10
                                        }
                                        GpuMode::ScanlineAccessingVRAM => {
                                            11
                                        }
                                        GpuMode::HorizontalBlank => {
                                            00
                                        }
                                        GpuMode::VerticalBlank => {
                                            01
                                        }
                                    };

                                    self.mapped_io[(addr - MAPPED_IO_START) as usize] | mode_flag
                                },
                                // SCY
                                0xFF42 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize]
                                },
                                // SCX
                                0xFF43 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize]
                                },
                                // LY
                                0xFF44 => {
                                    self.gpu_line
                                },
                                // BGP
                                0xFF47 => {
                                    eprintln!("Read of BGP is not implemented");
                                    0
                                },
                                // OBP0
                                0xFF48 => {
                                    eprintln!("Read of OBP0 is not implemented");
                                    0
                                },
                                // OBP1
                                0xFF49 => {
                                    eprintln!("Read of OBP1 is not implemented");
                                    0
                                },
                                _ => {
                                    unimplemented!("Read of Memory-mapped IO ${:04X?} is not implemented", addr);
                                    0
                                }
                            }
                        }
                    },
                    0x0E00 => {
                        // OAM
                        if 0xFE00 <= addr && addr < 0xFEA0 {
                            self.oam[(addr - 0xFE00) as usize]
                        } else {
                            unimplemented!()
                        }
                    },
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
            },
            0xC000 | 0xD000 => {
                // Internal RAM
                self.internal_ram[(addr - INTERNAL_RAM_START) as usize] = val;
            },
            0xF000 => {
                match addr & 0x0F00 {
                    0x0F00 => {
                        // zero page or memory-mapped IO
                        if addr == 0xFFFF {
                            // IRQ
                            self.interruption_enabled.write_u8(val);
                        } else if addr >= MEMORY_ZERO_START {
                            // zero page
                            self.memory_zero[(addr - MEMORY_ZERO_START) as usize] = val
                        } else {
                            match addr {
                                // P1
                                0xFF00 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize] = val;
                                },
                                // TAC
                                0xFF07 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize] = val;
                                },
                                // IF
                                0xFF0F => {
                                    self.interruption_occurred.write_u8(val);
                                },
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
                                },
                                // STAT
                                0xFF41 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize] = val
                                },
                                // SCY
                                0xFF42 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize] = val
                                },
                                // SCX
                                0xFF43 => {
                                    self.mapped_io[(addr - MAPPED_IO_START) as usize] = val
                                },
                                // LY
                                0xFF44 => {
                                },
                                // DMA
                                0xFF46 => {
                                    // The DMA Transfer (40*28 bit) from internal ROM orRAM ($0000-$F19F)
                                    // to the OAM (address $FE00-$FE9F).
                                    // Written value is XX of 0xXX00.
                                    let addr = (val as u16) * 0x100;
                                    for i in 0..40 {
                                        let src = addr + i;
                                        let dst = OAM_START + i;

                                        // TODO: We should cut off 4 bit
                                        let v = self.rb(src);
                                        self.wb(dst, v);
                                    }
                                    // eprintln!("DMA should take 160us");
                                }
                                // BGP
                                0xFF47 => {
                                    eprintln!("Write of BGP is not implemented");
                                },
                                // OBP0
                                0xFF48 => {
                                    eprintln!("Write of OBP0 is not implemented");
                                },
                                // OBP1
                                0xFF49 => {
                                    eprintln!("Write of OBP1 is not implemented");
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
                    },
                    0x0E00 => {
                        // OAM
                        if 0xFE00 <= addr && addr < 0xFEA0 {
                            self.oam[(addr - 0xFE00) as usize] = val;
                        } else {
                            unimplemented!()
                        }
                    },
                    _ => {
                        unimplemented!();
                    }
                }
            }
            _ => {
                unimplemented!();
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

            global_interruption_enabled: false,
            interruption_enabled: InterruptFlag::new(),
            interruption_occurred: InterruptFlag::new(),
            interruption_occurred_in_this_step: InterruptFlag::new(),
            joypad: Joypad::new(),

            read_from_bios: true,
            vram: [0; VRAM_SIZE as usize],
            internal_ram: [0; INTERNAL_RAM_SIZE as usize],
            oam: [0; OAM_SIZE as usize],
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
            0x01 => self.ld_xy_d16(Register::B, Register::C),
            0x03 => self.inc_xy(Register::B, Register::C),
            0x04 => self.inc_x(Register::B),
            0x05 => self.dec_x(Register::B),
            0x06 => self.ld_b_d8(),
            0x0A => self.ld_a_addr_bc(),
            0x0C => self.inc_x(Register::C),
            0x0D => self.dec_x(Register::C),
            0x0E => self.ld_c_d8(),
            0x11 => self.ld_xy_d16(Register::D, Register::E),
            0x13 => self.inc_xy(Register::D, Register::E),
            0x14 => self.inc_x(Register::D),
            0x15 => self.dec_x(Register::D),
            0x16 => self.ld_d_d8(),
            0x17 => self.rla(),
            0x18 => self.jr_r8(),
            0x19 => self.add_hl_de(),
            0x1A => self.ld_a_addr_de(),
            0x1C => self.inc_x(Register::E),
            0x1D => self.dec_x(Register::E),
            0x1E => self.ld_e_d8(),
            0x20 => self.jr_nz_r8(),
            0x21 => self.ld_xy_d16(Register::H, Register::L),
            0x22 => self.ld_addr_hl_plus_a(),
            0x23 => self.inc_xy(Register::H, Register::L),
            0x24 => self.inc_x(Register::H),
            0x25 => self.dec_x(Register::H),
            0x26 => self.ld_h_d8(),
            0x28 => self.jr_z_r8(),
            0x2A => self.ld_a_addr_hl_plus(),
            0x2C => self.inc_x(Register::L),
            0x2D => self.dec_x(Register::L),
            0x2E => self.ld_l_d8(),
            0x2F => self.cpl(),
            0x31 => self.ld_sp_d16(),
            0x32 => self.ld_addr_hl_minus_a(),
            0x35 => self.dec_addr_hl(),
            0x36 => self.ld_addr_hl_d8(),
            0x3C => self.inc_x(Register::A),
            0x3D => self.dec_x(Register::A),
            0x3E => self.ld_a_d8(),
            0x40 => self.ld_x_y(Register::B, Register::B),
            0x41 => self.ld_x_y(Register::B, Register::C),
            0x42 => self.ld_x_y(Register::B, Register::D),
            0x43 => self.ld_x_y(Register::B, Register::E),
            0x44 => self.ld_x_y(Register::B, Register::H),
            0x45 => self.ld_x_y(Register::B, Register::L),
            0x46 => unimplemented!(),
            0x47 => self.ld_x_y(Register::B, Register::A),
            0x48 => self.ld_x_y(Register::C, Register::B),
            0x49 => self.ld_x_y(Register::C, Register::C),
            0x4A => self.ld_x_y(Register::C, Register::D),
            0x4B => self.ld_x_y(Register::C, Register::E),
            0x4C => self.ld_x_y(Register::C, Register::H),
            0x4D => self.ld_x_y(Register::C, Register::L),
            0x4E => unimplemented!(),
            0x4F => self.ld_x_y(Register::C, Register::A),
            0x50 => self.ld_x_y(Register::D, Register::B),
            0x51 => self.ld_x_y(Register::D, Register::C),
            0x52 => self.ld_x_y(Register::D, Register::D),
            0x53 => self.ld_x_y(Register::D, Register::E),
            0x54 => self.ld_x_y(Register::D, Register::H),
            0x55 => self.ld_x_y(Register::D, Register::L),
            0x56 => unimplemented!(),
            0x57 => self.ld_x_y(Register::D, Register::A),
            0x58 => self.ld_x_y(Register::E, Register::B),
            0x59 => self.ld_x_y(Register::E, Register::C),
            0x5A => self.ld_x_y(Register::E, Register::D),
            0x5B => self.ld_x_y(Register::E, Register::E),
            0x5C => self.ld_x_y(Register::E, Register::H),
            0x5D => self.ld_x_y(Register::E, Register::L),
            0x5E => unimplemented!(),
            0x5F => self.ld_x_y(Register::E, Register::A),
            0x60 => self.ld_x_y(Register::H, Register::B),
            0x61 => self.ld_x_y(Register::H, Register::C),
            0x62 => self.ld_x_y(Register::H, Register::D),
            0x63 => self.ld_x_y(Register::H, Register::E),
            0x64 => self.ld_x_y(Register::H, Register::H),
            0x65 => self.ld_x_y(Register::H, Register::L),
            0x66 => unimplemented!(),
            0x67 => self.ld_x_y(Register::H, Register::A),
            0x68 => self.ld_x_y(Register::L, Register::B),
            0x69 => self.ld_x_y(Register::L, Register::C),
            0x6A => self.ld_x_y(Register::L, Register::D),
            0x6B => self.ld_x_y(Register::L, Register::E),
            0x6C => self.ld_x_y(Register::L, Register::H),
            0x6D => self.ld_x_y(Register::L, Register::L),
            0x6E => unimplemented!(),
            0x6F => self.ld_x_y(Register::L, Register::A),
            0x70 => self.ld_addr_hl_b(),
            0x71 => self.ld_addr_hl_c(),
            0x77 => self.ld_addr_hl_a(),
            0x78 => self.ld_x_y(Register::A, Register::B),
            0x79 => self.ld_x_y(Register::A, Register::C),
            0x7A => self.ld_x_y(Register::A, Register::D),
            0x7B => self.ld_x_y(Register::A, Register::E),
            0x7C => self.ld_x_y(Register::A, Register::H),
            0x7D => self.ld_x_y(Register::A, Register::L),
            0x7E => self.ld_a_addr_hl(),
            0x7F => self.ld_x_y(Register::A, Register::A),
            0x80 => self.add_a_b(),
            0x86 => self.add_addr_hl(),
            0x90 => self.sub_x(Register::B),
            0x91 => self.sub_x(Register::C),
            0x92 => self.sub_x(Register::D),
            0x93 => self.sub_x(Register::E),
            0x94 => self.sub_x(Register::H),
            0x95 => self.sub_x(Register::L),
            0x97 => self.sub_x(Register::A),
            0xA0 => self.and_x(Register::B),
            0xA1 => self.and_x(Register::C),
            0xA2 => self.and_x(Register::D),
            0xA3 => self.and_x(Register::E),
            0xA4 => self.and_x(Register::H),
            0xA5 => self.and_x(Register::L),
            0xA6 => unimplemented!(),
            0xA7 => self.and_x(Register::A),
            0xAF => self.xor_a(),
            0xB0 => self.or_b(),
            0xBE => self.cp_addr_hl(),
            0xC1 => self.pop_bc(),
            0xC2 => self.jp_nz_d16(),
            0xC3 => self.jp_d16(),
            0xC5 => self.push_bc(),
            0xC9 => self.ret(),
            0xCA => self.jp_z_d16(),
            0xC6 => self.add_a_d8(),
            0xCD => self.call_a16(),
            0xD1 => self.pop_de(),
            0xD5 => self.push_de(),
            0xD9 => self.reti(),
            0xE0 => self.ldh_addr_n_a(),
            0xE1 => self.pop_hl(),
            0xE2 => self.ldh_addr_c_a(),
            0xE5 => self.push_hl(),
            0xE6 => self.and_d8(),
            0xEA => self.ld_addr_d16_a(),
            0xF0 => self.ldh_a_addr_d8(),
            0xF1 => self.pop_af(),
            0xF2 => self.ldh_a_addr_c(),
            0xF3 => self.di(),
            0xF5 => self.push_af(),
            0xFA => self.ld_a_addr_d16(),
            0xFB => self.ei(),
            0xFE => self.cp_d8(),
            // Prefix CB
            0xCB => {
                let pc = self.read_r16(Register::PC);
                let op = self.read_u8_pc();
                match op {
                    0x11 => self.rl_c(),
                    0x23 => self.sla_e(),
                    0x27 => self.sla_a(),
                    0x37 => self.swap_a(),
                    0x47 => self.bit_n_x(0, Register::A),
                    0x5F => self.bit_n_x(3, Register::A),
                    0x67 => self.bit_n_x(4, Register::A),
                    0x6F => self.bit_n_x(5, Register::A),
                    0x77 => self.bit_n_x(6, Register::A),
                    0x7C => self.bit_n_x(7, Register::H),
                    0x7F => self.bit_n_x(7, Register::A),
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

        let screen_y = line;
        let scroll_y = self.rb(0xFF42);
        let scroll_x = self.rb(0xFF43);

        let buffer_y = line + scroll_y;

        // Background rendering
        if (self.rb(0xFF40) & (1 << 0)) != 0 {
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

            for screen_x in 0..160 {
                let buffer_x = scroll_x as u16 + screen_x;

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

        if (self.rb(0xFF40) & (1 << 1)) != 0 {
            let tile_set_addr = 0x8000 as u16;

            for sprite in 0..40 {
                let addr = 0xFE00 + 4 * sprite;
                let sprite_screen_y = (self.rb(addr) as i16) - 16;
                let sprite_screen_x = (self.rb(addr + 1) as i16) - 8;
                let tile_id = self.rb(addr + 2) as u16;
                let flags = self.rb(addr + 3);

                let inside_of_line = sprite_screen_y <= (screen_y as i16) && (screen_y as i16) < (sprite_screen_y + 8);
                if inside_of_line {

                    // eprintln!("{} {}", sprite_screen_x, sprite_screen_y);
                    let mut tile_addr_offset = 0 as u16;
                    for _ in 0..16 {
                        tile_addr_offset = tile_addr_offset.wrapping_add(tile_id);
                    }
                    let tile_addr = tile_set_addr.wrapping_add(tile_addr_offset);

                    // TODO: Palette
                    // TODO: Flip
                    for x in 0..8 {
                        let sx = sprite_screen_x + x;
                        if 0 <= sx && sx < 160 {
                            // Tile set for sprite is #1
                            let lx = x as u8;
                            let ly = ((screen_y as i16) - sprite_screen_y) as u8;

                            // 2 bytes consist of 1 line.
                            let line_addr1 = tile_addr + (2 * ly as u16);
                            let line_addr2 = line_addr1 + 1;

                            let line_val1 = self.rb(line_addr1);
                            let line_val2 = self.rb(line_addr2);
                            let rlx = 7 - lx;
                            let val = ((((line_val1 & (1 << rlx)) >> rlx) << 1) + ((line_val2 & (1 << rlx)) >> rlx)) as u8;

                            // TODO: Read value
                            self.gpu_screen[(160 * (screen_y as u16) + (sx as u16)) as usize] = val;
                        }
                    }
                }
            }
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
                        self.interruption_occurred_in_this_step.vblank = true;
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
        let mut cyclespent = 0;

        // First op
        self.dispatch();
        let cyclespent1 = self.get_proc_clock();
        self.set_proc_clock(0);
        self.gpu_step(cyclespent1);

        cyclespent += cyclespent1;
        self.interruption_occurred.or(self.interruption_occurred_in_this_step);

        // interruption check
        if self.global_interruption_enabled {
            if self.interruption_occurred_in_this_step.vblank && self.interruption_enabled.vblank {
                self.interruption_occurred.vblank = false;
                self.global_interruption_enabled = false;
                self.push_u16(self.read_r16(Register::PC));
                self.write_r16(Register::PC, 0x0040);
                self.set_proc_clock(12);

                let cyclespent2 = self.get_proc_clock();
                self.gpu_step(cyclespent2);
                cyclespent += cyclespent2;

                self.set_proc_clock(0);
            }
        }
        self.interruption_occurred_in_this_step.reset();

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

    pub fn set_button_a(&mut self, pressed: bool) -> () {
        self.joypad.a = pressed;
    }

    pub fn set_button_b(&mut self, pressed: bool) -> () {
        self.joypad.b = pressed;
    }

    pub fn set_button_left(&mut self, pressed: bool) -> () {
        self.joypad.left = pressed;
    }

    pub fn set_button_right(&mut self, pressed: bool) -> () {
        self.joypad.right = pressed;
    }

    pub fn set_button_up(&mut self, pressed: bool) -> () {
        self.joypad.up = pressed;
    }

    pub fn set_button_down(&mut self, pressed: bool) -> () {
        self.joypad.down = pressed;
    }

    pub fn set_button_start(&mut self, pressed: bool) -> () {
        self.joypad.start = pressed;
    }

    pub fn set_button_select(&mut self, pressed: bool) -> () {
        self.joypad.select = pressed;
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
