from kucoin.client import Market
from kucoin.client import Trade

# Sandbox Market
client = Market(url='https://openapi-sandbox.kucoin.com')
# Sandbox Trade
client = Trade(api_key, api_secret, api_passphrase, is_sandbox=True)

time = client.get_timestamp()
print(time)