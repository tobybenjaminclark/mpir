import sys
from PyQt5.QtWidgets import QApplication, QWidget, QHBoxLayout, QVBoxLayout, QTextEdit, QPushButton, QMainWindow, QStatusBar
from PyQt5.QtGui import QIcon, QTextCharFormat, QFont, QSyntaxHighlighter, QTextDocument, QPixmap
from PyQt5.QtCore import Qt, QRegExp, QSize


class PythonHighlighter(QSyntaxHighlighter):
    def __init__(self, parent=None):
        super(QSyntaxHighlighter, self).__init__(parent)

        keywordFormat = QTextCharFormat()
        keywordFormat.setForeground(Qt.cyan)
        keywordFormat.setFontWeight(QFont.Bold)

        keywordPatterns = ["funcdef", "suchthat", "end", "let", "trycast", "on", "return", "typedef", "into", "as", "set", "let"]
        self.highlightingRules = [(QRegExp(pattern), keywordFormat)
                                   for pattern in keywordPatterns]

        symbolFormat = QTextCharFormat()
        symbolFormat.setForeground(Qt.cyan)
        symbolFormat.setFontWeight(QFont.Bold)

        symbolPatterns = ["\\+", "-", "/", "\\*", "->", "::", "\\(", "\\)"]
        self.highlightingRules.extend((QRegExp(pattern), symbolFormat)
                                      for pattern in symbolPatterns)

        self.commentFormat = QTextCharFormat()
        self.commentFormat.setForeground(Qt.darkGreen)
        self.commentStartExpression = QRegExp(r'\|\s*')
        self.commentEndExpression = QRegExp(r'\|')


    def highlightBlock(self, text):
        for pattern, format in self.highlightingRules:
            expression = QRegExp(pattern)
            index = expression.indexIn(text)
            while index >= 0:
                length = expression.matchedLength()
                self.setFormat(index, length, format)
                index = expression.indexIn(text, index + length)

        self.setCurrentBlockState(0)

        startIndex = 0
        if self.previousBlockState() != 1:
            startIndex = self.commentStartExpression.indexIn(text)

        while startIndex >= 0:
            endIndex = self.commentEndExpression.indexIn(text, startIndex)
            if endIndex == -1:
                self.setCurrentBlockState(1)
                commentLength = len(text) - startIndex
            else:
                commentLength = endIndex - startIndex + self.commentEndExpression.matchedLength()

            self.setFormat(startIndex, commentLength, self.commentFormat)
            startIndex = self.commentStartExpression.indexIn(text, startIndex + commentLength)



class MyApp(QMainWindow):
    def __init__(self):
        super().__init__()

        self.initUI()

    def initUI(self):
        # Create central widget
        central_widget = QWidget()
        self.setCentralWidget(central_widget)

        # Create text boxes
        self.left_textbox = QTextEdit()
        self.right_textbox = QTextEdit()

        # Create Python syntax highlighter and associate it with the left_textbox
        self.highlighter = PythonHighlighter(self.left_textbox.document())

        # Create buttons with icons
        self.button1 = QPushButton()
        self.button2 = QPushButton()
        self.button3 = QPushButton()
        self.button4 = QPushButton()
        self.button5 = QPushButton()
        self.button6 = QPushButton()
        self.button7 = QPushButton()

        # Set icons and adjust their size
        icon_size = QSize(40, 40)  # Adjust the size as needed
        self.button1.setIcon(QIcon(QPixmap('planet.png').scaled(icon_size.width(), icon_size.height())))
        self.button1.setIconSize(icon_size)
        self.button2.setIcon(QIcon(QPixmap('save.png').scaled(icon_size.width(), icon_size.height())))
        self.button2.setIconSize(icon_size)
        self.button3.setIcon(QIcon(QPixmap('folder.png').scaled(icon_size.width(), icon_size.height())))
        self.button3.setIconSize(icon_size)
        self.button4.setIcon(QIcon(QPixmap('python.png').scaled(icon_size.width(), icon_size.height())))
        self.button4.setIconSize(icon_size)
        self.button5.setIcon(QIcon(QPixmap('icon1.png').scaled(icon_size.width(), icon_size.height())))
        self.button5.setIconSize(icon_size)
        self.button6.setIcon(QIcon(QPixmap('icon1.png').scaled(icon_size.width(), icon_size.height())))
        self.button6.setIconSize(icon_size)
        self.button7.setIcon(QIcon(QPixmap('icon1.png').scaled(icon_size.width(), icon_size.height())))
        self.button7.setIconSize(icon_size)
        
        # Set fixed size for buttons to make them square
        button_size = 64  # Adjust the size as needed
        self.button1.setFixedSize(button_size, button_size)
        self.button2.setFixedSize(button_size, button_size)
        self.button3.setFixedSize(button_size, button_size)
        self.button4.setFixedSize(button_size, button_size)
        self.button5.setFixedSize(button_size, button_size)
        self.button6.setFixedSize(button_size, button_size)
        self.button7.setFixedSize(button_size, button_size)

        # Add buttons to top bar
        left_buttons_layout = QHBoxLayout()
        left_buttons_layout.addWidget(self.button1)
        left_buttons_layout.addWidget(self.button2)
        left_buttons_layout.addWidget(self.button3)

        right_buttons_layout = QHBoxLayout()
        right_buttons_layout.addWidget(self.button4)
        right_buttons_layout.addWidget(self.button5)
        right_buttons_layout.addWidget(self.button6)
        right_buttons_layout.addWidget(self.button7)

        # Set up layout
        topbar_layout = QHBoxLayout()
        topbar_layout.addLayout(left_buttons_layout)
        topbar_layout.addStretch(1)  # Add stretchable space to push right-aligned buttons to the right
        topbar_layout.addLayout(right_buttons_layout)

        vbox = QVBoxLayout(central_widget)
        vbox.addLayout(topbar_layout)  # Add buttons layout first
        hbox = QHBoxLayout()
        hbox.addWidget(self.left_textbox)
        hbox.addWidget(self.right_textbox)
        vbox.addLayout(hbox)  # Add text boxes layout next

        # Add status bar
        self.statusBar = QStatusBar()
        self.setStatusBar(self.statusBar)

        self.setWindowTitle('PyQt5 App')
        self.setGeometry(100, 100, 800, 600)
        self.show()

if __name__ == '__main__':
    app = QApplication(sys.argv)
    ex = MyApp()
    sys.exit(app.exec_())
