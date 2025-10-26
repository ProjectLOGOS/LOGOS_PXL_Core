"""Check lazy-loaded libraries"""
try:
    import speech_recognition
    print('[+] speech_recognition available')
except:
    print('[-] speech_recognition missing')

try:
    import pyttsx3
    print('[+] pyttsx3 available')
except:
    print('[-] pyttsx3 missing')

try:
    import tkinter
    print('[+] tkinter available')
except:
    print('[-] tkinter missing')
