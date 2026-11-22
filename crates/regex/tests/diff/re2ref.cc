// Reads "hexpattern hextext" lines; prints what RE2 does with each:
// ERR, NOMATCH, or the start and end of every group (-1 -1 if unset).
#include <re2/re2.h>
#include <iostream>
#include <string>
#include <vector>

static std::string unhex(const std::string& h) {
  std::string out;
  for (size_t i = 0; i + 1 < h.size(); i += 2) out.push_back((char)std::stoi(h.substr(i, 2), nullptr, 16));
  return out;
}

int main() {
  std::string line;
  re2::RE2::Options opt;
  opt.set_log_errors(false);
  while (std::getline(std::cin, line)) {
    size_t sp = line.find(' ');
    std::string pat = unhex(line.substr(0, sp));
    std::string text = sp == std::string::npos ? "" : unhex(line.substr(sp + 1));
    re2::RE2 re(pat, opt);
    if (!re.ok()) {
      std::cout << "ERR\n";
      continue;
    }
    int n = re.NumberOfCapturingGroups() + 1;
    std::vector<absl::string_view> g(n);
    if (!re.Match(text, 0, text.size(), re2::RE2::UNANCHORED, g.data(), n)) {
      std::cout << "NOMATCH\n";
      continue;
    }
    for (int i = 0; i < n; i++) {
      if (g[i].data() == nullptr)
        std::cout << "-1 -1";
      else
        std::cout << (g[i].data() - text.data()) << " " << (g[i].data() - text.data() + g[i].size());
      std::cout << (i + 1 < n ? " " : "");
    }
    std::cout << "\n";
  }
}
