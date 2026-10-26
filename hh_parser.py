#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Парсер вакансий hh.ru по ТЗ (тз.txt).

Что делает:
  1) ходит по страницам поиска hh.ru (до 20 страниц) и собирает вакансии,
     сохраняя их в vacancies.json в формате из ТЗ;
  2) отбирает релевантные запросу вакансии (чтобы не попадали лишние,
     например "Сотрудник склада" на запрос "база данных"), лишние пишет
     в skipped.json;
  3) заходит до 200 вакансий и собирает "Ключевые навыки" -> vacancies_skills.json;
  4) считает статистику по навыкам (с учетом разных написаний: .net/.Net/.NET,
     c#/с#) -> stats.json.

Запуск:
    python hh_parser.py "C#" "база данных" "Frontend"

Зависимости: только стандартная библиотека + requests.
"""

import argparse
import json
import re
import sys
import time
import random
import unicodedata
from collections import Counter, OrderedDict, defaultdict
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urlencode, urljoin

try:
    import requests
except ImportError:
    print("Не установлен модуль requests. Выполните: pip install requests", file=sys.stderr)
    raise

# ---------------------------------------------------------------------------
# Настройки
# ---------------------------------------------------------------------------

BASE_URL = "https://hh.ru"
SEARCH_PATH = "/search/vacancy"

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language": "ru-RU,ru;q=0.9,en-US;q=0.8,en;q=0.7",
    "Sec-Fetch-Dest": "document",
    "Sec-Fetch-Mode": "navigate",
    "Sec-Fetch-Site": "none",
    "Sec-Fetch-User": "?1",
    "Upgrade-Insecure-Requests": "1",
}

# Кириллические буквы, похожие на латинские -> латиница.
# Используется и для поиска ("с#" == "c#"), и для склейки навыков (.NET == .net).
LOOKALIKE_TO_LATIN = str.maketrans({
    "а": "a", "в": "b", "с": "c", "е": "e", "ё": "e", "к": "k",
    "м": "m", "о": "o", "р": "p", "т": "t", "х": "x", "у": "y",
    "і": "i", "ѕ": "s", "ј": "j",
})

# Синонимы для отдельных слов запроса (ключи - нормализованное слово).
SYNONYMS = {
    "c#": ["c#", "c sharp", "csharp", "c♯"],
    "фронтенд": ["фронтенд", "frontend", "front-end", "front end"],
    "frontend": ["frontend", "front-end", "front end", "фронтенд"],
    "front-end": ["frontend", "front-end", "front end", "фронтенд"],
    "backend": ["backend", "back-end", "back end", "бэкенд", "бекенд"],
    "бэкенд": ["backend", "back-end", "back end", "бэкенд", "бекенд"],
    "fullstack": ["fullstack", "full stack", "full-stack", "фуллстек"],
    "фуллстек": ["fullstack", "full stack", "full-stack", "фуллстек"],
    ".net": [".net", "dotnet", "dot net", "дотнет"],
    "dotnet": [".net", "dotnet", "dot net", "дотнет"],
    "sql": ["sql"],
    "javascript": ["javascript", "js"],
    "js": ["javascript", "js"],
}

# Признаки страницы-капчи от hh.ru (отдаётся с кодом 200).
CAPTCHA_MARKERS = (
    "hcaptcha",
    "smartcaptcha",
    "подтвердите, что вы не робот",
    "текст с картинки",
    "проверка, что вы не робот",
)


VOID_TAGS = {
    "area", "base", "br", "col", "embed", "hr", "img", "input",
    "link", "meta", "param", "source", "track", "wbr",
}


# ---------------------------------------------------------------------------
# Минимальный DOM-парсер (без сторонних библиотек)
# ---------------------------------------------------------------------------

class Node:
    __slots__ = ("tag", "attrs", "children", "parent")

    def __init__(self, tag, attrs=None, parent=None):
        self.tag = tag
        self.attrs = dict(attrs or {})
        self.children = []   # Node | str
        self.parent = parent

    def text(self, joiner=" ") -> str:
        parts = []

        def walk(n):
            for c in n.children:
                if isinstance(c, str):
                    parts.append(c)
                else:
                    walk(c)

        walk(self)
        return clean_text(joiner.join(parts))

    def iter(self):
        for c in self.children:
            if isinstance(c, Node):
                yield c
                yield from c.iter()


class DomParser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = Node("#root")
        self.stack = [self.root]

    def handle_starttag(self, tag, attrs):
        node = Node(tag, attrs, self.stack[-1])
        self.stack[-1].children.append(node)
        if tag not in VOID_TAGS:
            self.stack.append(node)

    def handle_startendtag(self, tag, attrs):
        node = Node(tag, attrs, self.stack[-1])
        self.stack[-1].children.append(node)

    def handle_endtag(self, tag):
        for i in range(len(self.stack) - 1, 0, -1):
            if self.stack[i].tag == tag:
                del self.stack[i:]
                break

    def handle_data(self, data):
        if data:
            self.stack[-1].children.append(data)


def parse_html(html: str) -> Node:
    p = DomParser()
    p.feed(html)
    p.close()
    return p.root


def find_all(root: Node, **attrs):
    """Все узлы с указанными атрибутами, напр. find_all(root, **{'data-qa': 'x'})"""
    out = []
    for n in root.iter():
        if all(n.attrs.get(k) == v for k, v in attrs.items()):
            out.append(n)
    return out


def clean_text(s: str) -> str:
    """Убирает экранированные пробелы, неразрывные пробелы и прочий мусор."""
    if not s:
        return s
    for esc in ("\\u202f", "\\u2009", "\\u00a0", "\\u200b", "\\xa0"):
        s = s.replace(esc, " ")
    for ch in ("\u202f", "\u2009", "\u00a0", "\u200b", "\ufeff"):
        s = s.replace(ch, " ")
    s = re.sub(r"<!--.*?-->", " ", s, flags=re.S)
    s = re.sub(r"\s+", " ", s)
    return s.strip()


def normalize(s: str) -> str:
    s = unicodedata.normalize("NFKC", s or "")
    s = clean_text(s).lower()
    s = s.replace("ё", "е")
    return s


# ---------------------------------------------------------------------------
# HTTP
# ---------------------------------------------------------------------------

def is_captcha_page(text: str) -> bool:
    low = (text or "").lower()
    return any(m in low for m in CAPTCHA_MARKERS)


class HttpClient:
    def __init__(self, delay: float = 0.8, retries: int = 4,
                 timeout: int = 20, captcha_wait: float = 45.0):
        self.delay = delay
        self.retries = retries
        self.timeout = timeout
        self.captcha_wait = captcha_wait
        self.last_request = 0.0
        self.session = self._new_session()

    @staticmethod
    def _new_session() -> requests.Session:
        s = requests.Session()
        s.headers.update(HEADERS)
        return s

    def get(self, url: str) -> str:
        last_err = None
        for attempt in range(1, self.retries + 1):
            wait = self.delay + random.uniform(0, 0.35)
            pause = wait - (time.time() - self.last_request)
            if pause > 0:
                time.sleep(pause)
            self.last_request = time.time()
            try:
                resp = self.session.get(url, timeout=self.timeout)
            except requests.RequestException as e:
                last_err = e
                time.sleep(3 * attempt)
                continue
            if resp.status_code == 200:
                text = resp.text
                if is_captcha_page(text):
                    last_err = RuntimeError("hh.ru показал капчу/проверку")
                    if attempt < self.retries:
                        print(f"  ! капча от hh.ru, ждем {self.captcha_wait:.0f} c "
                              f"(попытка {attempt}/{self.retries - 1})...",
                              flush=True)
                        time.sleep(self.captcha_wait)
                        self.session = self._new_session()   # новая сессия/куки
                        continue
                    raise RuntimeError(
                        "hh.ru показал капчу. Сделайте паузу на несколько минут "
                        "и перезапустите с большим --delay (например --delay 2)."
                    )
                return text
            if resp.status_code in (403, 429, 503, 502, 504):
                last_err = RuntimeError(f"HTTP {resp.status_code} для {url}")
                if attempt < self.retries:
                    time.sleep(max(10, 5 * attempt))
                    self.session = self._new_session()
                continue
            if resp.status_code == 404:
                return ""
            last_err = RuntimeError(f"HTTP {resp.status_code} для {url}")
            time.sleep(2 * attempt)
        raise RuntimeError(f"Не удалось получить {url}: {last_err}")


# ---------------------------------------------------------------------------
# 1) Поиск: сбор вакансий со страниц выдачи
# ---------------------------------------------------------------------------

def build_search_url(query: str, page: int, per_page: int = 20) -> str:
    # Параметры взяты из примера в ТЗ (поиск по имени, компании и описанию).
    params = [
        ("text", query),
        ("search_field", "name"),
        ("search_field", "company_name"),
        ("search_field", "description"),
        ("enable_snippets", "false"),
        ("items_on_page", str(per_page)),
        ("page", str(page)),
    ]
    return BASE_URL + SEARCH_PATH + "?" + urlencode(params)


def parse_search_page(html: str):
    """-> (список сырых вакансий, всего найдено hh или None)"""
    root = parse_html(html)
    found_total = None
    m = re.search(r"Найдено\s+([\d\s\u00a0]+)\s*ваканс", clean_text(html))
    if m:
        found_total = int(re.sub(r"\D", "", m.group(1)))

    vacancies = []
    for art in find_all(root, **{"data-qa": "vacancy-serp__vacancy"}):
        title_link = None
        title = None
        for n in art.iter():
            qa = n.attrs.get("data-qa")
            if qa == "serp-item__title" and title_link is None:
                title_link = n.attrs.get("href")
            elif qa == "serp-item__title-text" and title is None:
                title = n.text()
        if not title_link or not title:
            continue

        employer = None
        for qa in ("vacancy-serp__vacancy-employer-text", "vacancy-serp__vacancy-employer"):
            nodes = find_all(art, **{"data-qa": qa})
            if nodes:
                employer = nodes[0].text()
                if employer:
                    break

        area = None
        nodes = find_all(art, **{"data-qa": "vacancy-serp__vacancy-address"})
        if nodes:
            area = nodes[0].text() or None

        salary = None
        for n in art.iter():
            if n.tag == "data" and n.attrs.get("value") and n.parent is not None:
                salary = n.parent.text()
                break

        url = urljoin(BASE_URL, title_link)
        vm = re.search(r"/vacancy/(\d+)", url)
        vacancies.append({
            "id": vm.group(1) if vm else None,
            "name": clean_text(title),
            "url": url,
            "employer": employer or None,
            "area": area or None,
            "salary": salary or None,
        })
    return vacancies, found_total


def collect_vacancies(client: HttpClient, query: str, max_pages: int):
    """Возвращает (сохранённые вакансии, пропущенные, сколько нашёл hh)."""
    raw = []
    seen = set()
    found_total = None
    pages_done = 0

    for page in range(max_pages):
        url = build_search_url(query, page)
        try:
            html = client.get(url)
        except RuntimeError as e:
            print(f"  ! страница {page + 1}: {e}")
            break
        items, total = parse_search_page(html)
        if total is not None and found_total is None:
            found_total = total
        if not items:
            print(f"  страница {page + 1}: пусто, останавливаемся")
            break
        pages_done += 1
        added = 0
        for v in items:
            key = v["id"] or v["url"]
            if key in seen:
                continue
            seen.add(key)
            raw.append(v)
            added += 1
        print(f"  страница {page + 1}/{max_pages}: +{added} (всего {len(raw)})")
        if added == 0:
            break
        if found_total is not None and len(raw) >= found_total:
            break

    kept, skipped = [], []
    for v in raw:
        ok, reason = check_relevance(v["name"], query)
        if ok:
            kept.append(v)
        else:
            skipped.append({**{k: v[k] for k in ("id", "name", "url")},
                            "reason": reason})
    print(f"  собрано {len(raw)}, релевантных {len(kept)}, отсеяно {len(skipped)} "
          f"(страниц прочитано: {pages_done})")
    return kept, skipped, found_total, len(raw)


# ---------------------------------------------------------------------------
# 2) Фильтр релевантности: не берём лишние вакансии
# ---------------------------------------------------------------------------

def compile_matcher(query: str):
    """Возвращает функцию match(title) -> bool.

    Все слова запроса должны встретиться в названии вакансии
    (с учетом основы слова: "база" найдет "базы", "баз данных").
    """
    tokens = [t for t in normalize(query).replace("+", " ").split() if t]
    groups = []
    for tok in tokens:
        if tok in SYNONYMS:
            groups.append({normalize(v) for v in SYNONYMS[tok]})
            continue
        if tok.isalpha() and len(tok) >= 4:
            stem = tok[:max(3, len(tok) - 2)]   # "база"->"баз", "данных"->"данн"
        else:
            stem = tok
        groups.append({stem, stem.translate(LOOKALIKE_TO_LATIN)})

    def match(title: str) -> bool:
        t = normalize(title)
        tl = t.translate(LOOKALIKE_TO_LATIN)
        return all(any(v in t or v in tl for v in g) for g in groups)

    return match


def check_relevance(name: str, query: str):
    matcher = compile_matcher(query)
    if matcher(name):
        return True, None
    return False, f"название не содержит слов запроса {query!r}"


# ---------------------------------------------------------------------------
# 3) Ключевые навыки со страницы вакансии
# ---------------------------------------------------------------------------

def parse_skills(html: str):
    if not html:
        return []
    root = parse_html(html)
    skills = []
    for n in find_all(root, **{"data-qa": "skills-element"}):
        s = n.text()
        if s:
            skills.append(s)
    if skills:
        return skills
    # запасной вариант - блок "Ключевые навыки"
    for n in root.iter():
        if n.tag in ("h1", "h2", "h3") and "Ключевые навыки" in n.text():
            parent = n.parent
            if parent is not None:
                for li in parent.iter():
                    if li.tag == "li":
                        s = li.text()
                        if s:
                            skills.append(s)
            break
    return skills


def collect_skills(client: HttpClient, vacancies, limit: int):
    result = []
    total = min(limit, len(vacancies))
    for i, v in enumerate(vacancies[:limit], 1):
        skills = []
        err = None
        try:
            html = client.get(v["url"])
            if not html:
                err = "вакансия недоступна (404)"
            else:
                tm = re.search(r"<title[^>]*>\s*([^<]*)", html)
                page_title = clean_text(tm.group(1)) if tm else ""
                if page_title.startswith(("Вакансия не найдена", "Страница не найдена", "Ошибка 404")):
                    err = "вакансия недоступна (снята с публикации)"
                else:
                    skills = parse_skills(html)
        except RuntimeError as e:
            err = str(e)
        if err and "капча" in err:
            # hh.ru перестал отдавать страницы - сохраняем хотя бы то, что успели
            print(f"  ! сбор навыков прерван: {err}", flush=True)
            exc = RuntimeError(err)
            exc.partial = result
            raise exc
        entry = OrderedDict([
            ("id", v["id"]),
            ("name", v["name"]),
            ("url", v["url"]),
            ("employer", v["employer"]),
            ("area", v["area"]),
            ("salary", v["salary"]),
            ("skills", skills),
        ])
        result.append(entry)
        note = f" навыков: {len(skills)}" if not err else f" ошибка: {err}"
        print(f"  [{i}/{total}] {v['name'][:60]}{note}", flush=True)
    return result


# ---------------------------------------------------------------------------
# 4) Статистика по навыкам
# ---------------------------------------------------------------------------

def canon_skill(skill: str) -> str:
    s = normalize(skill).translate(LOOKALIKE_TO_LATIN)
    return re.sub(r"\s+", " ", s).strip(" ,;.")


def build_stats(query: str, raw_total: int, parsed: list, with_skills: list) -> dict:
    vacancies_with_skills = sum(1 for v in with_skills if v["skills"])

    variants = defaultdict(Counter)   # канон -> счётчик оригинальных написаний
    counts = Counter()               # канон -> количество вакансий
    for v in with_skills:
        seen_here = set()
        for sk in v["skills"]:
            key = canon_skill(sk)
            if not key:
                continue
            variants[key][sk] += 1
            if key not in seen_here:
                seen_here.add(key)
                counts[key] += 1

    skills_list = []
    for key, cnt in counts.most_common():
        display = variants[key].most_common(1)[0][0]
        share = round(cnt * 100 / vacancies_with_skills, 1) if vacancies_with_skills else 0.0
        skills_list.append({"skill": display, "count": cnt, "share": share})

    return OrderedDict([
        ("query", query),
        ("vacancies_total", raw_total),
        ("vacancies_parsed", len(parsed)),
        ("vacancies_with_skills", vacancies_with_skills),
        ("distinct_skills", len(skills_list)),
        ("skills", skills_list),
    ])


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def slugify(s: str) -> str:
    s = normalize(s)
    mapping = {"c#": "c_sharp", "#": "_sharp", " ": "_"}
    out = []
    for ch in s:
        if ch.isalnum():
            out.append(ch)
        elif ch in mapping:
            out.append(mapping[ch])
        elif ch in "-_.":
            out.append("_")
    slug = re.sub(r"_+", "_", "".join(out)).strip("_")
    return slug or "query"


def save_json(path: Path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    print(f"  сохранено: {path}")


def run_query(client: HttpClient, query: str, out_root: Path,
              max_pages: int, limit: int) -> dict:
    print(f"\n=== Запрос: {query!r} ===")
    folder = out_root / slugify(query)

    kept, skipped, found_total, raw_total = collect_vacancies(client, query, max_pages)
    save_json(folder / "vacancies.json", kept)
    save_json(folder / "skipped.json", skipped)

    try:
        with_skills = collect_skills(client, kept, limit)
    except RuntimeError as e:
        partial = getattr(e, "partial", None)
        with_skills = partial if partial is not None else []
        print(f"  ! далее навыки не собирались: {e}")
    save_json(folder / "vacancies_skills.json", with_skills)

    stats = build_stats(query, raw_total, kept, with_skills)
    if found_total is not None:
        stats["found_on_hh"] = found_total
    save_json(folder / "stats.json", stats)

    print(f"  Итого: собрано {raw_total}, релевантных {len(kept)}, "
          f"с навыками {stats['vacancies_with_skills']}, "
          f"уникальных навыков {stats['distinct_skills']}")
    if skipped:
        examples = [s["name"] for s in skipped[:5]]
        print(f"  Отсеяно как нерелевантные ({len(skipped)}), например: "
              + "; ".join(examples))
    return stats


def main():
    if hasattr(sys.stdout, "reconfigure"):
        try:
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass

    ap = argparse.ArgumentParser(
        description="Парсер вакансий hh.ru с сбором ключевых навыков и статистикой."
    )
    ap.add_argument("queries", nargs="+", help='поисковые запросы, например: "C#" "база данных"')
    ap.add_argument("--pages", type=int, default=20, help="максимум страниц выдачи (по умолчанию 20)")
    ap.add_argument("--limit", type=int, default=200,
                    help="максимум вакансий, по которым собираются навыки (по умолчанию 200)")
    ap.add_argument("--delay", type=float, default=0.8,
                    help="пауза между запросами в секундах (по умолчанию 0.8)")
    ap.add_argument("--captcha-wait", type=float, default=45.0,
                    help="сколько ждать при капче от hh.ru, в секундах (по умолчанию 45)")
    ap.add_argument("--out", default="results", help="папка для результатов (по умолчанию results)")
    args = ap.parse_args()

    out_root = Path(args.out)
    client = HttpClient(delay=args.delay, captcha_wait=args.captcha_wait)
    started = time.time()

    all_stats = []
    for q in args.queries:
        try:
            all_stats.append(run_query(client, q, out_root, args.pages, args.limit))
        except RuntimeError as e:
            print(f"  !! Запрос {q!r} прерван: {e}", file=sys.stderr)

    print("\n=== Сводка ===")
    for s in all_stats:
        print(f"{s['query']}: собрано {s['vacancies_total']}, "
              f"отобрано {s['vacancies_parsed']}, "
              f"с навыками {s['vacancies_with_skills']}, "
              f"навыков-типов {s['distinct_skills']}")
        top = ", ".join(f"{i['skill']} ({i['count']})" for i in s["skills"][:5])
        if top:
            print(f"   топ: {top}")
    print(f"Готово за {time.time() - started:.0f} c.")


if __name__ == "__main__":
    main()
