#!/usr/bin/env python3
import os
import re
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC_DIR = ROOT / "FloatSpec" / "src"
OUT_SVG = ROOT / "FloatSpec_status.svg"
OUT_PNG = ROOT / "FloatSpec_status.png"
OUT_PDF = ROOT / "FloatSpec_status.pdf"


def read_file(p: Path) -> str:
    return p.read_text(encoding="utf-8", errors="ignore")


def strip_comments_and_strings(code: str) -> str:
    # Remove line comments `-- ...` and block comments `/- ... -/` (nested),
    # while preserving content inside string literals.
    i = 0
    n = len(code)
    out = []
    in_string = False
    escape = False
    block_depth = 0

    while i < n:
        c = code[i]

        if in_string:
            out.append(c)
            if escape:
                escape = False
            elif c == "\\":
                escape = True
            elif c == '"':
                in_string = False
            i += 1
            continue

        # If inside block comment, look for -/ and handle nesting
        if block_depth > 0:
            if c == "/" and i + 1 < n and code[i + 1] == "-":
                block_depth += 1
                i += 2
                continue
            if c == "-" and i + 1 < n and code[i + 1] == "/":
                block_depth -= 1
                i += 2
                continue
            # skip comment content
            i += 1
            continue

        # Not in string or block comment
        # Start of string
        if c == '"':
            in_string = True
            out.append(c)
            i += 1
            continue

        # Line comment
        if c == "-" and i + 1 < n and code[i + 1] == "-":
            # skip until newline
            i += 2
            while i < n and code[i] != "\n":
                i += 1
            # keep the newline
            if i < n:
                out.append("\n")
                i += 1
            continue

        # Block comment start
        if c == "/" and i + 1 < n and code[i + 1] == "-":
            block_depth = 1
            i += 2
            continue

        out.append(c)
        i += 1

    return "".join(out)


def count_items(code: str) -> tuple[int, int, int]:
    # Count theorems (theorem|lemma), definitions (def|definition), and sorry tokens
    stripped = strip_comments_and_strings(code)
    # Use MULTILINE and consider optional indentation and modifiers
    thm_pat = re.compile(r"^\s*(?:private|protected|scoped|local\s+)?(?:theorem|lemma)\b", re.MULTILINE)
    def_pat = re.compile(r"^\s*(?:private|protected|scoped|local|noncomputable\s+)?(?:def|definition)\b", re.MULTILINE)
    sorry_pat = re.compile(r"\bsorry\b")

    thms = len(thm_pat.findall(stripped))
    defs = len(def_pat.findall(stripped))
    sorries = len(sorry_pat.findall(stripped))
    return thms, defs, sorries


def scan_files() -> list[dict]:
    entries: list[dict] = []
    if not SRC_DIR.exists():
        return entries
    for p in sorted(SRC_DIR.rglob("*.lean")):
        rel_root = p.relative_to(ROOT)
        rel_src = p.relative_to(SRC_DIR)
        # Section is the first directory under src; files directly under src go to "Root"
        parts = rel_src.parts
        section = parts[0] if len(parts) > 1 else "Root"
        code = read_file(p)
        thms, defs, sorries = count_items(code)
        total_items = thms + defs
        unverified = min(sorries, total_items)
        verified = max(total_items - sorries, 0)
        entries.append({
            "section": section,
            "path": str(rel_root),
            "name": p.name,
            "thms": thms,
            "defs": defs,
            "sorries": sorries,
            "verified": verified,
            "unverified": unverified,
        })
    return entries


def layout(entries: list[dict]):
    # Layout parameters
    padding = 20
    line_height = 38
    title_gap = 6
    block_size = 12
    block_gap = 3
    block_row_gap = 6
    max_blocks = 20
    text_x = padding
    blocks_x = padding + 12

    # Split by section preserving order
    by_sec: dict[str, list[dict]] = {}
    for e in entries:
        by_sec.setdefault(e["section"], []).append(e)
    # Sort files in each section by name
    for sec in list(by_sec.keys()):
        by_sec[sec] = sorted(by_sec[sec], key=lambda d: d["name"].lower())

    # Global width; two columns layout
    width = 1080
    gutter = 40
    usable_width = width - 2 * padding - gutter
    col_width = usable_width // 2

    # Compute per-section heights
    def section_height(files: list[dict]) -> int:
        if not files:
            return 0
        y = line_height  # header
        for e in files:
            red_blocks = math.ceil(e["unverified"] / 3) if e["unverified"] > 0 else 0
            green_blocks = math.ceil(e["verified"] / 3) if e["verified"] > 0 else 0
            total_blocks = red_blocks + green_blocks
            block_rows = max(1, math.ceil(total_blocks / max_blocks))
            y += line_height + (block_rows - 1) * (block_size + block_row_gap)
        return y

    # Assign sections to two columns in import order: Core -> Calc -> others
    ordered_secs = sorted(by_sec.keys(), key=lambda s: s.lower())
    left_secs: list[str] = []
    right_secs: list[str] = []
    if "Core" in ordered_secs:
        left_secs.append("Core")
        ordered_secs.remove("Core")
    if "Calc" in ordered_secs:
        right_secs.append("Calc")
        ordered_secs.remove("Calc")
    h_left = sum(section_height(by_sec[s]) for s in left_secs)
    h_right = sum(section_height(by_sec[s]) for s in right_secs)
    for s in ordered_secs:
        h_s = section_height(by_sec[s])
        if h_left <= h_right:
            left_secs.append(s)
            h_left += h_s
        else:
            right_secs.append(s)
            h_right += h_s

    height_left = padding + h_left + padding
    height_right = padding + h_right + padding
    height = max(height_left, height_right)

    # Column x origins
    x_left = padding
    x_right = padding + col_width + gutter

    return {
        "padding": padding,
        "line_height": line_height,
        "title_gap": title_gap,
        "block_size": block_size,
        "block_gap": block_gap,
        "block_row_gap": block_row_gap,
        "max_blocks": max_blocks,
        "text_x": text_x,
        "blocks_x": blocks_x,
        "by_sec": by_sec,
        "left_secs": left_secs,
        "right_secs": right_secs,
        "width": width,
        "height": height,
        "gutter": gutter,
        "col_width": col_width,
        "x_left": x_left,
        "x_right": x_right,
    }


def render_svg(entries: list[dict]) -> str:
    L = layout(entries)
    padding = L["padding"]
    line_height = L["line_height"]
    title_gap = L["title_gap"]
    block_size = L["block_size"]
    block_gap = L["block_gap"]
    block_row_gap = L["block_row_gap"]
    max_blocks = L["max_blocks"]
    base_text_x = L["text_x"]
    base_blocks_x = L["blocks_x"]
    by_sec = L["by_sec"]
    left_secs = L["left_secs"]
    right_secs = L["right_secs"]
    width = L["width"]
    height = L["height"]
    x_left = L["x_left"]
    x_right = L["x_right"]
    # Independent y positions per column
    y_left = L["padding"]
    y_right = L["padding"]
    parts = [
        f"<svg xmlns='http://www.w3.org/2000/svg' width='{width}' height='{height}' viewBox='0 0 {width} {height}'>",
        "<style>"
        "text { font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, 'Liberation Mono', 'Courier New', monospace; font-size: 13px; fill: #222; }"
        ".sec { font-weight: 700; font-size: 18px; }"
        ".file { font-weight: 600; }"
        "</style>"
    ]

    # Render left column sections
    for sec in left_secs:
        files = by_sec.get(sec, [])
        if not files:
            continue
        parts.append(f"<text class='sec' x='{x_left + base_text_x}' y='{y_left}'>{sec}</text>")
        y_left += line_height
        for e in files:
            total_items = e['thms'] + e['defs']
            label = f"{e['name']} (All={total_items}, unverified={e['unverified']})"
            parts.append(f"<text class='file' x='{x_left + base_text_x}' y='{y_left - title_gap}'>{label}</text>")

            red_remaining = math.ceil(e["unverified"] / 3) if e["unverified"] > 0 else 0
            green_remaining = math.ceil(e["verified"] / 3) if e["verified"] > 0 else 0
            total_blocks = red_remaining + green_remaining
            block_rows = max(1, math.ceil(total_blocks / max_blocks))

            for r in range(block_rows):
                row_blocks = min(max_blocks, red_remaining + green_remaining)
                disp_red = min(red_remaining, row_blocks)
                disp_green = max(0, row_blocks - disp_red)
                row_y = y_left + r * (block_size + block_row_gap)
                for i in range(disp_red):
                    x = x_left + base_blocks_x + i * (block_size + block_gap)
                    parts.append(f"<rect x='{x}' y='{row_y}' width='{block_size}' height='{block_size}' fill='#e74c3c' rx='2' ry='2'/>")
                for i in range(disp_green):
                    x = x_left + base_blocks_x + (disp_red + i) * (block_size + block_gap)
                    parts.append(f"<rect x='{x}' y='{row_y}' width='{block_size}' height='{block_size}' fill='#2ecc71' rx='2' ry='2'/>")
                red_remaining -= disp_red
                green_remaining -= disp_green

            y_left += line_height + (block_rows - 1) * (block_size + block_row_gap)

    # Render right column sections
    for sec in right_secs:
        files = by_sec.get(sec, [])
        if not files:
            continue
        parts.append(f"<text class='sec' x='{x_right + base_text_x}' y='{y_right}'>{sec}</text>")
        y_right += line_height
        for e in files:
            total_items = e['thms'] + e['defs']
            label = f"{e['name']} (All={total_items}, unverified={e['unverified']})"
            parts.append(f"<text class='file' x='{x_right + base_text_x}' y='{y_right - title_gap}'>{label}</text>")

            red_remaining = math.ceil(e["unverified"] / 3) if e["unverified"] > 0 else 0
            green_remaining = math.ceil(e["verified"] / 3) if e["verified"] > 0 else 0
            total_blocks = red_remaining + green_remaining
            block_rows = max(1, math.ceil(total_blocks / max_blocks))

            for r in range(block_rows):
                row_blocks = min(max_blocks, red_remaining + green_remaining)
                disp_red = min(red_remaining, row_blocks)
                disp_green = max(0, row_blocks - disp_red)
                row_y = y_right + r * (block_size + block_row_gap)
                for i in range(disp_red):
                    x = x_right + base_blocks_x + i * (block_size + block_gap)
                    parts.append(f"<rect x='{x}' y='{row_y}' width='{block_size}' height='{block_size}' fill='#e74c3c' rx='2' ry='2'/>")
                for i in range(disp_green):
                    x = x_right + base_blocks_x + (disp_red + i) * (block_size + block_gap)
                    parts.append(f"<rect x='{x}' y='{row_y}' width='{block_size}' height='{block_size}' fill='#2ecc71' rx='2' ry='2'/>")
                red_remaining -= disp_red
                green_remaining -= disp_green

            y_right += line_height + (block_rows - 1) * (block_size + block_row_gap)

    parts.append("</svg>")
    return "".join(parts)


def render_png(entries: list[dict], out: Path) -> None:
    from PIL import Image, ImageDraw, ImageFont
    L = layout(entries)
    padding = L["padding"]
    line_height = L["line_height"]
    title_gap = L["title_gap"]
    block_size = L["block_size"]
    block_gap = L["block_gap"]
    block_row_gap = L["block_row_gap"]
    max_blocks = L["max_blocks"]
    base_text_x = L["text_x"]
    base_blocks_x = L["blocks_x"]
    by_sec = L["by_sec"]
    left_secs = L["left_secs"]
    right_secs = L["right_secs"]
    width = L["width"]
    height = L["height"]
    x_left = L["x_left"]
    x_right = L["x_right"]
    y_left = padding
    y_right = padding

    img = Image.new("RGB", (width, height), "#ffffff")
    draw = ImageDraw.Draw(img)

    # Try to load a monospace font; fallback to default
    font = None
    sec_font = None
    for path in [
        "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf",
        "/usr/share/fonts/truetype/liberation/LiberationMono-Regular.ttf",
        "/usr/share/fonts/truetype/ubuntu/UbuntuMono-R.ttf",
    ]:
        if Path(path).exists():
            try:
                font = ImageFont.truetype(path, 13)
                sec_font = ImageFont.truetype(path, 18)
                break
            except Exception:
                pass
    if font is None:
        font = ImageFont.load_default()
        sec_font = font

    # Colors
    text_color = (34, 34, 34)
    red = (231, 76, 60)
    green = (46, 204, 113)

    # Left column sections
    for sec in left_secs:
        files = by_sec.get(sec, [])
        if not files:
            continue
        draw.text((x_left + base_text_x, y_left), sec, fill=text_color, font=sec_font)
        y_left += line_height
        for e in files:
            total_items = e['thms'] + e['defs']
            label = f"{e['name']} (All={total_items}, unverified={e['unverified']})"
            draw.text((x_left + base_text_x, y_left - title_gap - 12), label, fill=text_color, font=font)

            red_remaining = math.ceil(e["unverified"] / 3) if e["unverified"] > 0 else 0
            green_remaining = math.ceil(e["verified"] / 3) if e["verified"] > 0 else 0
            total_blocks = red_remaining + green_remaining
            block_rows = max(1, math.ceil(total_blocks / max_blocks))

            for r in range(block_rows):
                row_blocks = min(max_blocks, red_remaining + green_remaining)
                disp_red = min(red_remaining, row_blocks)
                disp_green = max(0, row_blocks - disp_red)
                row_y = y_left + r * (block_size + block_row_gap)
                for i in range(disp_red):
                    x = x_left + base_blocks_x + i * (block_size + block_gap)
                    draw.rounded_rectangle([x, row_y, x + block_size, row_y + block_size], radius=2, fill=red)
                for i in range(disp_green):
                    x = x_left + base_blocks_x + (disp_red + i) * (block_size + block_gap)
                    draw.rounded_rectangle([x, row_y, x + block_size, row_y + block_size], radius=2, fill=green)
                red_remaining -= disp_red
                green_remaining -= disp_green

            y_left += line_height + (block_rows - 1) * (block_size + block_row_gap)

    # Right column sections
    for sec in right_secs:
        files = by_sec.get(sec, [])
        if not files:
            continue
        draw.text((x_right + base_text_x, y_right), sec, fill=text_color, font=sec_font)
        y_right += line_height
        for e in files:
            total_items = e['thms'] + e['defs']
            label = f"{e['name']} (All={total_items}, unverified={e['unverified']})"
            draw.text((x_right + base_text_x, y_right - title_gap - 12), label, fill=text_color, font=font)

            red_remaining = math.ceil(e["unverified"] / 3) if e["unverified"] > 0 else 0
            green_remaining = math.ceil(e["verified"] / 3) if e["verified"] > 0 else 0
            total_blocks = red_remaining + green_remaining
            block_rows = max(1, math.ceil(total_blocks / max_blocks))

            for r in range(block_rows):
                row_blocks = min(max_blocks, red_remaining + green_remaining)
                disp_red = min(red_remaining, row_blocks)
                disp_green = max(0, row_blocks - disp_red)
                row_y = y_right + r * (block_size + block_row_gap)
                for i in range(disp_red):
                    x = x_right + base_blocks_x + i * (block_size + block_gap)
                    draw.rounded_rectangle([x, row_y, x + block_size, row_y + block_size], radius=2, fill=red)
                for i in range(disp_green):
                    x = x_right + base_blocks_x + (disp_red + i) * (block_size + block_gap)
                    draw.rounded_rectangle([x, row_y, x + block_size, row_y + block_size], radius=2, fill=green)
                red_remaining -= disp_red
                green_remaining -= disp_green

            y_right += line_height + (block_rows - 1) * (block_size + block_row_gap)

    img.save(out, format="PNG")


def render_pdf(entries: list[dict], out: Path) -> None:
    try:
        from reportlab.pdfgen import canvas
        from reportlab.lib.colors import Color
        from reportlab.pdfbase import pdfmetrics
    except Exception as e:
        # Fallback: embed the PNG into a PDF for portability
        try:
            render_png(entries, OUT_PNG)
            from PIL import Image
            img = Image.open(OUT_PNG)
            img.save(out, "PDF")
            return
        except Exception as e2:
            raise RuntimeError(f"PDF render failed: {e}; PNG->PDF fallback failed: {e2}")

    L = layout(entries)
    padding = L["padding"]
    line_height = L["line_height"]
    title_gap = L["title_gap"]
    block_size = L["block_size"]
    block_gap = L["block_gap"]
    block_row_gap = L["block_row_gap"]
    max_blocks = L["max_blocks"]
    base_text_x = L["text_x"]
    base_blocks_x = L["blocks_x"]
    by_sec = L["by_sec"]
    left_secs = L["left_secs"]
    right_secs = L["right_secs"]
    width = float(L["width"])  # points
    height = float(L["height"])  # points
    x_left = float(L["x_left"]) 
    x_right = float(L["x_right"]) 

    c = canvas.Canvas(str(out), pagesize=(width, height))

    # Colors
    text_color = Color(34/255, 34/255, 34/255)
    red = Color(231/255, 76/255, 60/255)
    green = Color(46/255, 204/255, 113/255)

    def draw_text(x: float, y_top: float, text: str, size: int, bold: bool = False):
        # Convert top-left y to ReportLab baseline y, accounting for ascent so that
        # the text's top aligns with y_top (to match PNG/SVG layout).
        font_name = "Courier-Bold" if bold else "Courier"
        c.setFont(font_name, size)
        ascent = 0.0
        try:
            ascent = (pdfmetrics.getAscent(font_name) or 0) * (size / 1000.0)
        except Exception:
            ascent = 0.0
        y = height - y_top - ascent
        c.setFillColor(text_color)
        c.drawString(x, y, text)

    def draw_rect(x: float, y_top: float, w: float, h: float, color: Color):
        y = height - y_top - h
        c.setFillColor(color)
        c.roundRect(x, y, w, h, radius=2, fill=1, stroke=0)

    # Left column
    y_left = float(padding)
    for sec in left_secs:
        files = by_sec.get(sec, [])
        if not files:
            continue
        draw_text(x_left + base_text_x, y_left, sec, size=18, bold=True)
        y_left += line_height
        for e in files:
            total_items = e['thms'] + e['defs']
            label = f"{e['name']} (All={total_items}, unverified={e['unverified']})"
            # approximate baseline alignment similar to PNG: shift up by ~title_gap
            draw_text(x_left + base_text_x, y_left - title_gap - 12, label, size=13, bold=False)

            red_remaining = math.ceil(e["unverified"] / 3) if e["unverified"] > 0 else 0
            green_remaining = math.ceil(e["verified"] / 3) if e["verified"] > 0 else 0
            total_blocks = red_remaining + green_remaining
            block_rows = max(1, math.ceil(total_blocks / max_blocks))
            for r in range(block_rows):
                row_blocks = min(max_blocks, red_remaining + green_remaining)
                disp_red = min(red_remaining, row_blocks)
                disp_green = max(0, row_blocks - disp_red)
                row_y = y_left + r * (block_size + block_row_gap)
                for i in range(disp_red):
                    x = x_left + base_blocks_x + i * (block_size + block_gap)
                    draw_rect(x, row_y, block_size, block_size, red)
                for i in range(disp_green):
                    x = x_left + base_blocks_x + (disp_red + i) * (block_size + block_gap)
                    draw_rect(x, row_y, block_size, block_size, green)
                red_remaining -= disp_red
                green_remaining -= disp_green
            y_left += line_height + (block_rows - 1) * (block_size + block_row_gap)

    # Right column
    y_right = float(padding)
    for sec in right_secs:
        files = by_sec.get(sec, [])
        if not files:
            continue
        draw_text(x_right + base_text_x, y_right, sec, size=18, bold=True)
        y_right += line_height
        for e in files:
            total_items = e['thms'] + e['defs']
            label = f"{e['name']} (All={total_items}, unverified={e['unverified']})"
            draw_text(x_right + base_text_x, y_right - title_gap - 12, label, size=13, bold=False)

            red_remaining = math.ceil(e["unverified"] / 3) if e["unverified"] > 0 else 0
            green_remaining = math.ceil(e["verified"] / 3) if e["verified"] > 0 else 0
            total_blocks = red_remaining + green_remaining
            block_rows = max(1, math.ceil(total_blocks / max_blocks))
            for r in range(block_rows):
                row_blocks = min(max_blocks, red_remaining + green_remaining)
                disp_red = min(red_remaining, row_blocks)
                disp_green = max(0, row_blocks - disp_red)
                row_y = y_right + r * (block_size + block_row_gap)
                for i in range(disp_red):
                    x = x_right + base_blocks_x + i * (block_size + block_gap)
                    draw_rect(x, row_y, block_size, block_size, red)
                for i in range(disp_green):
                    x = x_right + base_blocks_x + (disp_red + i) * (block_size + block_gap)
                    draw_rect(x, row_y, block_size, block_size, green)
                red_remaining -= disp_red
                green_remaining -= disp_green
            y_right += line_height + (block_rows - 1) * (block_size + block_row_gap)

    c.showPage()
    c.save()


def main():
    entries = scan_files()
    svg = render_svg(entries)
    OUT_SVG.write_text(svg, encoding="utf-8")
    print(f"Wrote {OUT_SVG}")
    # Prefer vector PDF outputs; PNG is optional for quick preview
    try:
        render_pdf(entries, OUT_PDF)
        print(f"Wrote {OUT_PDF}")
    except Exception as e:
        print(f"PDF render failed: {e}")

    # Additionally, emit a vector PDF for each top-level section (directory under src)
    try:
        secs = sorted({e["section"] for e in entries})
        for sec in secs:
            sec_entries = [e for e in entries if e["section"] == sec]
            out = ROOT / f"FloatSpec_{sec}_status.pdf"
            try:
                render_pdf(sec_entries, out)
                print(f"Wrote {out}")
            except Exception as se:
                print(f"PDF render for section '{sec}' failed: {se}")
    except Exception as e:
        print(f"Per-section PDF generation failed: {e}")

    # Keep PNG generation as best-effort for convenience
    try:
        render_png(entries, OUT_PNG)
        print(f"Wrote {OUT_PNG}")
    except Exception as e:
        print(f"PNG render failed: {e}")


if __name__ == "__main__":
    main()
